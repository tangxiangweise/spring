/*
 * Copyright 2002-2019 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.springframework.beans.factory.support;

import java.beans.PropertyDescriptor;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.security.PrivilegedActionException;
import java.security.PrivilegedExceptionAction;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

import org.springframework.beans.BeanUtils;
import org.springframework.beans.BeanWrapper;
import org.springframework.beans.BeanWrapperImpl;
import org.springframework.beans.BeansException;
import org.springframework.beans.MutablePropertyValues;
import org.springframework.beans.PropertyAccessorUtils;
import org.springframework.beans.PropertyValue;
import org.springframework.beans.PropertyValues;
import org.springframework.beans.TypeConverter;
import org.springframework.beans.factory.Aware;
import org.springframework.beans.factory.BeanClassLoaderAware;
import org.springframework.beans.factory.BeanCreationException;
import org.springframework.beans.factory.BeanCurrentlyInCreationException;
import org.springframework.beans.factory.BeanDefinitionStoreException;
import org.springframework.beans.factory.BeanFactory;
import org.springframework.beans.factory.BeanFactoryAware;
import org.springframework.beans.factory.BeanNameAware;
import org.springframework.beans.factory.FactoryBean;
import org.springframework.beans.factory.InitializingBean;
import org.springframework.beans.factory.ObjectFactory;
import org.springframework.beans.factory.UnsatisfiedDependencyException;
import org.springframework.beans.factory.config.AutowireCapableBeanFactory;
import org.springframework.beans.factory.config.BeanDefinition;
import org.springframework.beans.factory.config.BeanPostProcessor;
import org.springframework.beans.factory.config.ConfigurableBeanFactory;
import org.springframework.beans.factory.config.ConstructorArgumentValues;
import org.springframework.beans.factory.config.DependencyDescriptor;
import org.springframework.beans.factory.config.InstantiationAwareBeanPostProcessor;
import org.springframework.beans.factory.config.SmartInstantiationAwareBeanPostProcessor;
import org.springframework.beans.factory.config.TypedStringValue;
import org.springframework.core.DefaultParameterNameDiscoverer;
import org.springframework.core.GenericTypeResolver;
import org.springframework.core.MethodParameter;
import org.springframework.core.ParameterNameDiscoverer;
import org.springframework.core.PriorityOrdered;
import org.springframework.core.ResolvableType;
import org.springframework.util.ClassUtils;
import org.springframework.util.ObjectUtils;
import org.springframework.util.ReflectionUtils;
import org.springframework.util.StringUtils;

/**
 * Abstract bean factory superclass that implements default bean creation,
 * with the full capabilities specified by the {@link RootBeanDefinition} class.
 * Implements the {@link org.springframework.beans.factory.config.AutowireCapableBeanFactory}
 * interface in addition to AbstractBeanFactory's {@link #createBean} method.
 *
 * <p>Provides bean creation (with constructor resolution), property population,
 * wiring (including autowiring), and initialization. Handles runtime bean
 * references, resolves managed collections, calls initialization methods, etc.
 * Supports autowiring constructors, properties by name, and properties by type.
 *
 * <p>The main template method to be implemented by subclasses is
 * {@link #resolveDependency(DependencyDescriptor, String, Set, TypeConverter)},
 * used for autowiring by type. In case of a factory which is capable of searching
 * its bean definitions, matching beans will typically be implemented through such
 * a search. For other factory styles, simplified matching algorithms can be implemented.
 *
 * <p>Note that this class does <i>not</i> assume or implement bean definition
 * registry capabilities. See {@link DefaultListableBeanFactory} for an implementation
 * of the {@link org.springframework.beans.factory.ListableBeanFactory} and
 * {@link BeanDefinitionRegistry} interfaces, which represent the API and SPI
 * view of such a factory, respectively.
 *
 * @author Rod Johnson
 * @author Juergen Hoeller
 * @author Rob Harrop
 * @author Mark Fisher
 * @author Costin Leau
 * @author Chris Beams
 * @author Sam Brannen
 * @see RootBeanDefinition
 * @see DefaultListableBeanFactory
 * @see BeanDefinitionRegistry
 * @since 13.02.2004
 */
public abstract class AbstractAutowireCapableBeanFactory extends AbstractBeanFactory
        implements AutowireCapableBeanFactory {

    /**
     * Strategy for creating bean instances
     */
    private InstantiationStrategy instantiationStrategy = new CglibSubclassingInstantiationStrategy();

    /**
     * Resolver strategy for method parameter names
     */
    private ParameterNameDiscoverer parameterNameDiscoverer = new DefaultParameterNameDiscoverer();

    /**
     * Whether to automatically try to resolve circular references between beans
     */
    private boolean allowCircularReferences = true;

    /**
     * Whether to resort to injecting a raw bean instance in case of circular reference,
     * even if the injected bean eventually got wrapped.
     */
    private boolean allowRawInjectionDespiteWrapping = false;

    /**
     * Dependency types to ignore on dependency check and autowire, as Set of
     * Class objects: for example, String. Default is none.
     */
    private final Set<Class<?>> ignoredDependencyTypes = new HashSet<Class<?>>();

    /**
     * Dependency interfaces to ignore on dependency check and autowire, as Set of
     * Class objects. By default, only the BeanFactory interface is ignored.
     */
    private final Set<Class<?>> ignoredDependencyInterfaces = new HashSet<Class<?>>();

    /**
     * Cache of unfinished FactoryBean instances: FactoryBean name --> BeanWrapper
     */
    private final ConcurrentMap<String, BeanWrapper> factoryBeanInstanceCache =
            new ConcurrentHashMap<String, BeanWrapper>(16);

    /**
     * Cache of filtered PropertyDescriptors: bean Class -> PropertyDescriptor array
     */
    private final ConcurrentMap<Class<?>, PropertyDescriptor[]> filteredPropertyDescriptorsCache =
            new ConcurrentHashMap<Class<?>, PropertyDescriptor[]>(256);


    /**
     * Create a new AbstractAutowireCapableBeanFactory.
     */
    public AbstractAutowireCapableBeanFactory() {
        super();
        ignoreDependencyInterface(BeanNameAware.class);
        ignoreDependencyInterface(BeanFactoryAware.class);
        ignoreDependencyInterface(BeanClassLoaderAware.class);
    }

    /**
     * Create a new AbstractAutowireCapableBeanFactory with the given parent.
     *
     * @param parentBeanFactory parent bean factory, or {@code null} if none
     */
    public AbstractAutowireCapableBeanFactory(BeanFactory parentBeanFactory) {
        this();
        setParentBeanFactory(parentBeanFactory);
    }


    /**
     * Set the instantiation strategy to use for creating bean instances.
     * Default is CglibSubclassingInstantiationStrategy.
     *
     * @see CglibSubclassingInstantiationStrategy
     */
    public void setInstantiationStrategy(InstantiationStrategy instantiationStrategy) {
        this.instantiationStrategy = instantiationStrategy;
    }

    /**
     * Return the instantiation strategy to use for creating bean instances.
     */
    protected InstantiationStrategy getInstantiationStrategy() {
        return this.instantiationStrategy;
    }

    /**
     * Set the ParameterNameDiscoverer to use for resolving method parameter
     * names if needed (e.g. for constructor names).
     * <p>Default is a {@link DefaultParameterNameDiscoverer}.
     */
    public void setParameterNameDiscoverer(ParameterNameDiscoverer parameterNameDiscoverer) {
        this.parameterNameDiscoverer = parameterNameDiscoverer;
    }

    /**
     * Return the ParameterNameDiscoverer to use for resolving method parameter
     * names if needed.
     */
    protected ParameterNameDiscoverer getParameterNameDiscoverer() {
        return this.parameterNameDiscoverer;
    }

    /**
     * Set whether to allow circular references between beans - and automatically
     * try to resolve them.
     * <p>Note that circular reference resolution means that one of the involved beans
     * will receive a reference to another bean that is not fully initialized yet.
     * This can lead to subtle and not-so-subtle side effects on initialization;
     * it does work fine for many scenarios, though.
     * <p>Default is "true". Turn this off to throw an exception when encountering
     * a circular reference, disallowing them completely.
     * <p><b>NOTE:</b> It is generally recommended to not rely on circular references
     * between your beans. Refactor your application logic to have the two beans
     * involved delegate to a third bean that encapsulates their common logic.
     */
    public void setAllowCircularReferences(boolean allowCircularReferences) {
        this.allowCircularReferences = allowCircularReferences;
    }

    /**
     * Set whether to allow the raw injection of a bean instance into some other
     * bean's property, despite the injected bean eventually getting wrapped
     * (for example, through AOP auto-proxying).
     * <p>This will only be used as a last resort in case of a circular reference
     * that cannot be resolved otherwise: essentially, preferring a raw instance
     * getting injected over a failure of the entire bean wiring process.
     * <p>Default is "false", as of Spring 2.0. Turn this on to allow for non-wrapped
     * raw beans injected into some of your references, which was Spring 1.2's
     * (arguably unclean) default behavior.
     * <p><b>NOTE:</b> It is generally recommended to not rely on circular references
     * between your beans, in particular with auto-proxying involved.
     *
     * @see #setAllowCircularReferences
     */
    public void setAllowRawInjectionDespiteWrapping(boolean allowRawInjectionDespiteWrapping) {
        this.allowRawInjectionDespiteWrapping = allowRawInjectionDespiteWrapping;
    }

    /**
     * Ignore the given dependency type for autowiring:
     * for example, String. Default is none.
     */
    public void ignoreDependencyType(Class<?> type) {
        this.ignoredDependencyTypes.add(type);
    }

    /**
     * Ignore the given dependency interface for autowiring.
     * <p>This will typically be used by application contexts to register
     * dependencies that are resolved in other ways, like BeanFactory through
     * BeanFactoryAware or ApplicationContext through ApplicationContextAware.
     * <p>By default, only the BeanFactoryAware interface is ignored.
     * For further types to ignore, invoke this method for each type.
     *
     * @see org.springframework.beans.factory.BeanFactoryAware
     * @see org.springframework.context.ApplicationContextAware
     */
    public void ignoreDependencyInterface(Class<?> ifc) {
        this.ignoredDependencyInterfaces.add(ifc);
    }

    @Override
    public void copyConfigurationFrom(ConfigurableBeanFactory otherFactory) {
        super.copyConfigurationFrom(otherFactory);
        if (otherFactory instanceof AbstractAutowireCapableBeanFactory) {
            AbstractAutowireCapableBeanFactory otherAutowireFactory =
                    (AbstractAutowireCapableBeanFactory) otherFactory;
            this.instantiationStrategy = otherAutowireFactory.instantiationStrategy;
            this.allowCircularReferences = otherAutowireFactory.allowCircularReferences;
            this.ignoredDependencyTypes.addAll(otherAutowireFactory.ignoredDependencyTypes);
            this.ignoredDependencyInterfaces.addAll(otherAutowireFactory.ignoredDependencyInterfaces);
        }
    }


    //-------------------------------------------------------------------------
    // Typical methods for creating and populating external bean instances
    //-------------------------------------------------------------------------

    @Override
    @SuppressWarnings("unchecked")
    public <T> T createBean(Class<T> beanClass) throws BeansException {
        // Use prototype bean definition, to avoid registering bean as dependent bean.
        RootBeanDefinition bd = new RootBeanDefinition(beanClass);
        bd.setScope(SCOPE_PROTOTYPE);
        bd.allowCaching = ClassUtils.isCacheSafe(beanClass, getBeanClassLoader());
        return (T) createBean(beanClass.getName(), bd, null);
    }

    @Override
    public void autowireBean(Object existingBean) {
        // Use non-singleton bean definition, to avoid registering bean as dependent bean.
        RootBeanDefinition bd = new RootBeanDefinition(ClassUtils.getUserClass(existingBean));
        bd.setScope(BeanDefinition.SCOPE_PROTOTYPE);
        bd.allowCaching = ClassUtils.isCacheSafe(bd.getBeanClass(), getBeanClassLoader());
        BeanWrapper bw = new BeanWrapperImpl(existingBean);
        initBeanWrapper(bw);
        populateBean(bd.getBeanClass().getName(), bd, bw);
    }

    @Override
    public Object configureBean(Object existingBean, String beanName) throws BeansException {
        markBeanAsCreated(beanName);
        BeanDefinition mbd = getMergedBeanDefinition(beanName);
        RootBeanDefinition bd = null;
        if (mbd instanceof RootBeanDefinition) {
            RootBeanDefinition rbd = (RootBeanDefinition) mbd;
            bd = (rbd.isPrototype() ? rbd : rbd.cloneBeanDefinition());
        }
        if (!mbd.isPrototype()) {
            if (bd == null) {
                bd = new RootBeanDefinition(mbd);
            }
            bd.setScope(BeanDefinition.SCOPE_PROTOTYPE);
            bd.allowCaching = ClassUtils.isCacheSafe(ClassUtils.getUserClass(existingBean), getBeanClassLoader());
        }
        BeanWrapper bw = new BeanWrapperImpl(existingBean);
        initBeanWrapper(bw);
        populateBean(beanName, bd, bw);
        return initializeBean(beanName, existingBean, bd);
    }

    @Override
    public Object resolveDependency(DependencyDescriptor descriptor, String requestingBeanName) throws BeansException {
        return resolveDependency(descriptor, requestingBeanName, null, null);
    }


    //-------------------------------------------------------------------------
    // Specialized methods for fine-grained control over the bean lifecycle
    //-------------------------------------------------------------------------

    @Override
    public Object createBean(Class<?> beanClass, int autowireMode, boolean dependencyCheck) throws BeansException {
        // Use non-singleton bean definition, to avoid registering bean as dependent bean.
        RootBeanDefinition bd = new RootBeanDefinition(beanClass, autowireMode, dependencyCheck);
        bd.setScope(BeanDefinition.SCOPE_PROTOTYPE);
        return createBean(beanClass.getName(), bd, null);
    }

    @Override
    public Object autowire(Class<?> beanClass, int autowireMode, boolean dependencyCheck) throws BeansException {
        // Use non-singleton bean definition, to avoid registering bean as dependent bean.
        final RootBeanDefinition bd = new RootBeanDefinition(beanClass, autowireMode, dependencyCheck);
        bd.setScope(BeanDefinition.SCOPE_PROTOTYPE);
        if (bd.getResolvedAutowireMode() == AUTOWIRE_CONSTRUCTOR) {
            return autowireConstructor(beanClass.getName(), bd, null, null).getWrappedInstance();
        } else {
            Object bean;
            final BeanFactory parent = this;
            if (System.getSecurityManager() != null) {
                bean = AccessController.doPrivileged(new PrivilegedAction<Object>() {
                    @Override
                    public Object run() {
                        return getInstantiationStrategy().instantiate(bd, null, parent);
                    }
                }, getAccessControlContext());
            } else {
                bean = getInstantiationStrategy().instantiate(bd, null, parent);
            }
            populateBean(beanClass.getName(), bd, new BeanWrapperImpl(bean));
            return bean;
        }
    }

    @Override
    public void autowireBeanProperties(Object existingBean, int autowireMode, boolean dependencyCheck)
            throws BeansException {

        if (autowireMode == AUTOWIRE_CONSTRUCTOR) {
            throw new IllegalArgumentException("AUTOWIRE_CONSTRUCTOR not supported for existing bean instance");
        }
        // Use non-singleton bean definition, to avoid registering bean as dependent bean.
        RootBeanDefinition bd =
                new RootBeanDefinition(ClassUtils.getUserClass(existingBean), autowireMode, dependencyCheck);
        bd.setScope(BeanDefinition.SCOPE_PROTOTYPE);
        BeanWrapper bw = new BeanWrapperImpl(existingBean);
        initBeanWrapper(bw);
        populateBean(bd.getBeanClass().getName(), bd, bw);
    }

    @Override
    public void applyBeanPropertyValues(Object existingBean, String beanName) throws BeansException {
        markBeanAsCreated(beanName);
        BeanDefinition bd = getMergedBeanDefinition(beanName);
        BeanWrapper bw = new BeanWrapperImpl(existingBean);
        initBeanWrapper(bw);
        applyPropertyValues(beanName, bd, bw, bd.getPropertyValues());
    }

    @Override
    public Object initializeBean(Object existingBean, String beanName) {
        return initializeBean(beanName, existingBean, null);
    }

    @Override
    public Object applyBeanPostProcessorsBeforeInitialization(Object existingBean, String beanName)
            throws BeansException {

        Object result = existingBean;
        for (BeanPostProcessor processor : getBeanPostProcessors()) {
            result = processor.postProcessBeforeInitialization(result, beanName);
            if (result == null) {
                return result;
            }
        }
        return result;
    }

    @Override
    public Object applyBeanPostProcessorsAfterInitialization(Object existingBean, String beanName)
            throws BeansException {

        Object result = existingBean;
        for (BeanPostProcessor processor : getBeanPostProcessors()) {
            /**
             * bean 初始化后置处理
             */
            result = processor.postProcessAfterInitialization(result, beanName);
            if (result == null) {
                return result;
            }
        }
        return result;
    }

    @Override
    public void destroyBean(Object existingBean) {
        new DisposableBeanAdapter(existingBean, getBeanPostProcessors(), getAccessControlContext()).destroy();
    }


    //---------------------------------------------------------------------
    // Implementation of relevant AbstractBeanFactory template methods
    //---------------------------------------------------------------------

    /**
     * Central method of this class: creates a bean instance,
     * populates the bean instance, applies post-processors, etc.
     * @see #doCreateBean
     */
    /**
     * createBean 和 getBean 方法类似，基本上都是空壳方法，
     * createBean 的逻辑稍微多点，做了如下处理：
     * 1. 解析 bean 类型
     * 2. 处理 lookup-method 和 replace-method 配置
     * 3. 在 bean 初始化前应用后置处理，若后置处理返回的 bean 不为空，则直接返回
     * 4. 若上一步后置处理返回的 bean 为空，则调用 doCreateBean 创建 bean 实例
     */
    @Override
    protected Object createBean(String beanName, RootBeanDefinition mbd, Object[] args) throws BeanCreationException {
        if (logger.isDebugEnabled()) {
            logger.debug("Creating instance of bean '" + beanName + "'");
        }
        RootBeanDefinition mbdToUse = mbd;

        // Make sure bean class is actually resolved at this point, and
        // clone the bean definition in case of a dynamically resolved Class
        // which cannot be stored in the shared merged bean definition.
        /**
         * 解析bean的类型
         */
        Class<?> resolvedClass = resolveBeanClass(mbd, beanName);
        if (resolvedClass != null && !mbd.hasBeanClass() && mbd.getBeanClassName() != null) {
            mbdToUse = new RootBeanDefinition(mbd);
            mbdToUse.setBeanClass(resolvedClass);
        }

        // Prepare method overrides.
        try {
            /**
             * 处理 lookup-method 和 replace-method 配置，Spring 将这两个配置统称为 override method
             */
            mbdToUse.prepareMethodOverrides();
        } catch (BeanDefinitionValidationException ex) {
            throw new BeanDefinitionStoreException(mbdToUse.getResourceDescription(),
                    beanName, "Validation of method overrides failed", ex);
        }

        try {
            // Give BeanPostProcessors a chance to return a proxy instead of the target bean instance.
            /**
             * 在bean初始化前应用后置处理，如果后置处理返回的bean不为空，则直接返回
             */
            Object bean = resolveBeforeInstantiation(beanName, mbdToUse);
            if (bean != null) {
                return bean;
            }
        } catch (Throwable ex) {
            throw new BeanCreationException(mbdToUse.getResourceDescription(), beanName,
                    "BeanPostProcessor before instantiation of bean failed", ex);
        }
        /**
         * 调用doCreateBean创建bean
         */
        Object beanInstance = doCreateBean(beanName, mbdToUse, args);
        if (logger.isDebugEnabled()) {
            logger.debug("Finished creating instance of bean '" + beanName + "'");
        }
        return beanInstance;
    }

    /**
     * Actually create the specified bean. Pre-creation processing has already happened
     * at this point, e.g. checking {@code postProcessBeforeInstantiation} callbacks.
     * <p>Differentiates between default bean instantiation, use of a
     * factory method, and autowiring a constructor.
     * @param beanName the name of the bean
     * @param mbd the merged bean definition for the bean
     * @param args explicit arguments to use for constructor or factory method invocation
     * @return a new instance of the bean
     * @throws BeanCreationException if the bean could not be created
     * @see #instantiateBean
     * @see #instantiateUsingFactoryMethod
     * @see #autowireConstructor
     */
    /**
     * 该方法执行流程 ：
     * 1. 从缓存中获取 BeanWrapper 实现类对象，并清理相关记录
     * 2. 若未命中缓存，则创建 bean 实例，并将实例包裹在 BeanWrapper 实现类对象中返回
     * 3. 应用 MergedBeanDefinitionPostProcessor 后置处理器相关逻辑
     * 4. 根据条件决定是否提前暴露 bean 的早期引用（early reference），用于处理循环依赖问题
     * 5. 调用 populateBean 方法向 bean 实例中填充属性
     * 6. 调用 initializeBean 方法完成余下的初始化工作
     * 7. 注册销毁逻辑
     */
    protected Object doCreateBean(final String beanName, final RootBeanDefinition mbd, final Object[] args)
            throws BeanCreationException {

        // Instantiate the bean.
        /**
         * BeanWrapper 是一个基础接口，由接口名可看出这个接口的实现类用于包裹bean实例
         * 通过BeanWrapper的实现类可以方便的设置／获取bean实例的属性
         */
        BeanWrapper instanceWrapper = null;
        if (mbd.isSingleton()) {
            /**
             * 从缓存中获取BeanWrapper并清理相关记录
             */
            instanceWrapper = this.factoryBeanInstanceCache.remove(beanName);
        }
        if (instanceWrapper == null) {
            /**
             * 创建bean实例，并将实例包裹在BeanWrapper实现类对象中返回，createBeanInstance中包含三种创建bean实例方式：
             * 		1. 通过工厂方法创建bean实例
             * 		2. 通过构造方法自动注入( autowire by constructor)的方式创建bean实例
             * 		3. 通过无参构造方法创建bean实例
             *
             * 	若bean的配置信息中配置了lookup-method 和 replace-method ,则会使用 CGLIB
             * 	增强bean实例。
             *
             */
            instanceWrapper = createBeanInstance(beanName, mbd, args);
        }
        /**
         * 此处的bean可以认为是一个原始的bean实例，暂未填充属性
         */
        final Object bean = (instanceWrapper != null ? instanceWrapper.getWrappedInstance() : null);
        Class<?> beanType = (instanceWrapper != null ? instanceWrapper.getWrappedClass() : null);
        mbd.resolvedTargetType = beanType;

        // Allow post-processors to modify the merged bean definition.
        /**
         * 这里又遇到后置处理，此处的后置处理是用于处理已"合并的BeanDefinition"
         */
        synchronized (mbd.postProcessingLock) {
            if (!mbd.postProcessed) {
                try {
                    applyMergedBeanDefinitionPostProcessors(mbd, beanType, beanName);
                } catch (Throwable ex) {
                    throw new BeanCreationException(mbd.getResourceDescription(), beanName,
                            "Post-processing of merged bean definition failed", ex);
                }
                mbd.postProcessed = true;
            }
        }

        // Eagerly cache singletons to be able to resolve circular references
        // even when triggered by lifecycle interfaces like BeanFactoryAware.
        /**
         * earlySingletonExposure 是一个重要的变量，该变量用于表示是否提前暴露单例bean，用于解决循环依赖
         * earlySingletonExposure 由三个条件综合而成，如下 ：
         * 	条件1：mbd.isSingleton() - 表示 bean 是否是单例类型
         * 	条件2：allowCircularReferences - 是否允许循环依赖
         * 	条件3：isSingletonCurrentlyInCreation(beanName) - 当前 bean 是否处于创建的状态中
         *
         * 	earlySingletonExposure = 条件1 && 条件2 && 条件3  = 单例 && 是否允许循环依赖 && 是否存于创建状态中。
         *
         */
        boolean earlySingletonExposure = (mbd.isSingleton() && this.allowCircularReferences &&
                isSingletonCurrentlyInCreation(beanName));
        if (earlySingletonExposure) {
            if (logger.isDebugEnabled()) {
                logger.debug("Eagerly caching bean '" + beanName +
                        "' to allow for resolving potential circular references");
            }
            /**
             * 添加工厂对象到 singletonFactories 缓存中
             */
            addSingletonFactory(beanName, new ObjectFactory<Object>() {
                @Override
                public Object getObject() throws BeansException {
                    /**
                     * 获取早期bean的引用，如果bean中的方法被AOP切点所匹配到，此时AOP相关逻辑会介入
                     */
                    return getEarlyBeanReference(beanName, mbd, bean);
                }
            });
        }

        // Initialize the bean instance.
        Object exposedObject = bean;
        try {
            /**
             * 向bean实例中填充属性，populateBean 方法也是一个很重要的方法
             */
            populateBean(beanName, mbd, instanceWrapper);
            if (exposedObject != null) {
                /**
                 * 进行余下的初始化工作，详情如下：
                 * 	1. 判断bean是否实现了BeanNameAware｜BeanFactoryAware｜BeanClassLoaderAware 等接口方法
                 * 	2. 应用 bean 初始化前置操作
                 * 	3. 如果 bean 实现了 InitializingBean 接口，则执行 afterPropertiesSet方法。
                 * 	   如果用户配置了init-method，则调用相关方法执行自定义初始化逻辑
                 * 	4. 应用 bean 初始化后置操作
                 * 	另外AOP相关逻辑也会在该方法中织入切面逻辑，此时exposedObject就变成了一个代理对象
                 */
                exposedObject = initializeBean(beanName, exposedObject, mbd);
            }
        } catch (Throwable ex) {
            if (ex instanceof BeanCreationException && beanName.equals(((BeanCreationException) ex).getBeanName())) {
                throw (BeanCreationException) ex;
            } else {
                throw new BeanCreationException(
                        mbd.getResourceDescription(), beanName, "Initialization of bean failed", ex);
            }
        }

        if (earlySingletonExposure) {
            Object earlySingletonReference = getSingleton(beanName, false);
            if (earlySingletonReference != null) {
                /**
                 * 若initializeBean 方法未改变 exposedObject 的引用，则此处的条件为 true
                 */
                if (exposedObject == bean) {
                    exposedObject = earlySingletonReference;
                } else if (!this.allowRawInjectionDespiteWrapping && hasDependentBean(beanName)) {
                    String[] dependentBeans = getDependentBeans(beanName);
                    Set<String> actualDependentBeans = new LinkedHashSet<String>(dependentBeans.length);
                    for (String dependentBean : dependentBeans) {
                        if (!removeSingletonIfCreatedForTypeCheckOnly(dependentBean)) {
                            actualDependentBeans.add(dependentBean);
                        }
                    }
                    if (!actualDependentBeans.isEmpty()) {
                        throw new BeanCurrentlyInCreationException(beanName,
                                "Bean with name '" + beanName + "' has been injected into other beans [" +
                                        StringUtils.collectionToCommaDelimitedString(actualDependentBeans) +
                                        "] in its raw version as part of a circular reference, but has eventually been " +
                                        "wrapped. This means that said other beans do not use the final version of the " +
                                        "bean. This is often the result of over-eager type matching - consider using " +
                                        "'getBeanNamesOfType' with the 'allowEagerInit' flag turned off, for example.");
                    }
                }
            }
        }

        // Register bean as disposable.
        try {
            /**
             * 注册销毁逻辑
             */
            registerDisposableBeanIfNecessary(beanName, bean, mbd);
        } catch (BeanDefinitionValidationException ex) {
            throw new BeanCreationException(
                    mbd.getResourceDescription(), beanName, "Invalid destruction signature", ex);
        }

        return exposedObject;
    }

    @Override
    protected Class<?> predictBeanType(String beanName, RootBeanDefinition mbd, Class<?>... typesToMatch) {
        Class<?> targetType = determineTargetType(beanName, mbd, typesToMatch);

        // Apply SmartInstantiationAwareBeanPostProcessors to predict the
        // eventual type after a before-instantiation shortcut.
        if (targetType != null && !mbd.isSynthetic() && hasInstantiationAwareBeanPostProcessors()) {
            for (BeanPostProcessor bp : getBeanPostProcessors()) {
                if (bp instanceof SmartInstantiationAwareBeanPostProcessor) {
                    SmartInstantiationAwareBeanPostProcessor ibp = (SmartInstantiationAwareBeanPostProcessor) bp;
                    Class<?> predicted = ibp.predictBeanType(targetType, beanName);
                    if (predicted != null && (typesToMatch.length != 1 || FactoryBean.class != typesToMatch[0] ||
                            FactoryBean.class.isAssignableFrom(predicted))) {
                        return predicted;
                    }
                }
            }
        }
        return targetType;
    }

    /**
     * Determine the target type for the given bean definition.
     *
     * @param beanName     the name of the bean (for error handling purposes)
     * @param mbd          the merged bean definition for the bean
     * @param typesToMatch the types to match in case of internal type matching purposes
     *                     (also signals that the returned {@code Class} will never be exposed to application code)
     * @return the type for the bean if determinable, or {@code null} otherwise
     */
    protected Class<?> determineTargetType(String beanName, RootBeanDefinition mbd, Class<?>... typesToMatch) {
        Class<?> targetType = mbd.getTargetType();
        if (targetType == null) {
            targetType = (mbd.getFactoryMethodName() != null ?
                    getTypeForFactoryMethod(beanName, mbd, typesToMatch) :
                    resolveBeanClass(mbd, beanName, typesToMatch));
            if (ObjectUtils.isEmpty(typesToMatch) || getTempClassLoader() == null) {
                mbd.resolvedTargetType = targetType;
            }
        }
        return targetType;
    }

    /**
     * Determine the target type for the given bean definition which is based on
     * a factory method. Only called if there is no singleton instance registered
     * for the target bean already.
     * <p>This implementation determines the type matching {@link #createBean}'s
     * different creation strategies. As far as possible, we'll perform static
     * type checking to avoid creation of the target bean.
     *
     * @param beanName     the name of the bean (for error handling purposes)
     * @param mbd          the merged bean definition for the bean
     * @param typesToMatch the types to match in case of internal type matching purposes
     *                     (also signals that the returned {@code Class} will never be exposed to application code)
     * @return the type for the bean if determinable, or {@code null} otherwise
     * @see #createBean
     */
    protected Class<?> getTypeForFactoryMethod(String beanName, RootBeanDefinition mbd, Class<?>... typesToMatch) {
        ResolvableType cachedReturnType = mbd.factoryMethodReturnType;
        if (cachedReturnType != null) {
            return cachedReturnType.resolve();
        }

        Class<?> factoryClass;
        boolean isStatic = true;

        String factoryBeanName = mbd.getFactoryBeanName();
        if (factoryBeanName != null) {
            if (factoryBeanName.equals(beanName)) {
                throw new BeanDefinitionStoreException(mbd.getResourceDescription(), beanName,
                        "factory-bean reference points back to the same bean definition");
            }
            // Check declared factory method return type on factory class.
            factoryClass = getType(factoryBeanName);
            isStatic = false;
        } else {
            // Check declared factory method return type on bean class.
            factoryClass = resolveBeanClass(mbd, beanName, typesToMatch);
        }

        if (factoryClass == null) {
            return null;
        }
        factoryClass = ClassUtils.getUserClass(factoryClass);

        // If all factory methods have the same return type, return that type.
        // Can't clearly figure out exact method due to type converting / autowiring!
        Class<?> commonType = null;
        Method uniqueCandidate = null;
        int minNrOfArgs = mbd.getConstructorArgumentValues().getArgumentCount();
        Method[] candidates = ReflectionUtils.getUniqueDeclaredMethods(factoryClass);
        for (Method candidate : candidates) {
            if (Modifier.isStatic(candidate.getModifiers()) == isStatic && mbd.isFactoryMethod(candidate) &&
                    candidate.getParameterTypes().length >= minNrOfArgs) {
                // Declared type variables to inspect?
                if (candidate.getTypeParameters().length > 0) {
                    try {
                        // Fully resolve parameter names and argument values.
                        Class<?>[] paramTypes = candidate.getParameterTypes();
                        String[] paramNames = null;
                        ParameterNameDiscoverer pnd = getParameterNameDiscoverer();
                        if (pnd != null) {
                            paramNames = pnd.getParameterNames(candidate);
                        }
                        ConstructorArgumentValues cav = mbd.getConstructorArgumentValues();
                        Set<ConstructorArgumentValues.ValueHolder> usedValueHolders =
                                new HashSet<ConstructorArgumentValues.ValueHolder>(paramTypes.length);
                        Object[] args = new Object[paramTypes.length];
                        for (int i = 0; i < args.length; i++) {
                            ConstructorArgumentValues.ValueHolder valueHolder = cav.getArgumentValue(
                                    i, paramTypes[i], (paramNames != null ? paramNames[i] : null), usedValueHolders);
                            if (valueHolder == null) {
                                valueHolder = cav.getGenericArgumentValue(null, null, usedValueHolders);
                            }
                            if (valueHolder != null) {
                                args[i] = valueHolder.getValue();
                                usedValueHolders.add(valueHolder);
                            }
                        }
                        Class<?> returnType = AutowireUtils.resolveReturnTypeForFactoryMethod(
                                candidate, args, getBeanClassLoader());
                        if (returnType != null) {
                            uniqueCandidate = (commonType == null && returnType == candidate.getReturnType() ?
                                    candidate : null);
                            commonType = ClassUtils.determineCommonAncestor(returnType, commonType);
                            if (commonType == null) {
                                // Ambiguous return types found: return null to indicate "not determinable".
                                return null;
                            }
                        }
                    } catch (Throwable ex) {
                        if (logger.isDebugEnabled()) {
                            logger.debug("Failed to resolve generic return type for factory method: " + ex);
                        }
                    }
                } else {
                    uniqueCandidate = (commonType == null ? candidate : null);
                    commonType = ClassUtils.determineCommonAncestor(candidate.getReturnType(), commonType);
                    if (commonType == null) {
                        // Ambiguous return types found: return null to indicate "not determinable".
                        return null;
                    }
                }
            }
        }

        if (commonType == null) {
            return null;
        }
        // Common return type found: all factory methods return same type. For a non-parameterized
        // unique candidate, cache the full type declaration context of the target factory method.
        cachedReturnType = (uniqueCandidate != null ?
                ResolvableType.forMethodReturnType(uniqueCandidate) : ResolvableType.forClass(commonType));
        mbd.factoryMethodReturnType = cachedReturnType;
        return cachedReturnType.resolve();
    }

    /**
     * This implementation attempts to query the FactoryBean's generic parameter metadata
     * if present to determine the object type. If not present, i.e. the FactoryBean is
     * declared as a raw type, checks the FactoryBean's {@code getObjectType} method
     * on a plain instance of the FactoryBean, without bean properties applied yet.
     * If this doesn't return a type yet, a full creation of the FactoryBean is
     * used as fallback (through delegation to the superclass's implementation).
     * <p>The shortcut check for a FactoryBean is only applied in case of a singleton
     * FactoryBean. If the FactoryBean instance itself is not kept as singleton,
     * it will be fully created to check the type of its exposed object.
     */
    @Override
    protected Class<?> getTypeForFactoryBean(String beanName, RootBeanDefinition mbd) {
        String factoryBeanName = mbd.getFactoryBeanName();
        String factoryMethodName = mbd.getFactoryMethodName();

        if (factoryBeanName != null) {
            if (factoryMethodName != null) {
                // Try to obtain the FactoryBean's object type from its factory method declaration
                // without instantiating the containing bean at all.
                BeanDefinition fbDef = getBeanDefinition(factoryBeanName);
                if (fbDef instanceof AbstractBeanDefinition) {
                    AbstractBeanDefinition afbDef = (AbstractBeanDefinition) fbDef;
                    if (afbDef.hasBeanClass()) {
                        Class<?> result = getTypeForFactoryBeanFromMethod(afbDef.getBeanClass(), factoryMethodName);
                        if (result != null) {
                            return result;
                        }
                    }
                }
            }
            // If not resolvable above and the referenced factory bean doesn't exist yet,
            // exit here - we don't want to force the creation of another bean just to
            // obtain a FactoryBean's object type...
            if (!isBeanEligibleForMetadataCaching(factoryBeanName)) {
                return null;
            }
        }

        // Let's obtain a shortcut instance for an early getObjectType() call...
        FactoryBean<?> fb = (mbd.isSingleton() ?
                getSingletonFactoryBeanForTypeCheck(beanName, mbd) :
                getNonSingletonFactoryBeanForTypeCheck(beanName, mbd));

        if (fb != null) {
            // Try to obtain the FactoryBean's object type from this early stage of the instance.
            Class<?> result = getTypeForFactoryBean(fb);
            if (result != null) {
                return result;
            } else {
                // No type found for shortcut FactoryBean instance:
                // fall back to full creation of the FactoryBean instance.
                return super.getTypeForFactoryBean(beanName, mbd);
            }
        }

        if (factoryBeanName == null && mbd.hasBeanClass()) {
            // No early bean instantiation possible: determine FactoryBean's type from
            // static factory method signature or from class inheritance hierarchy...
            if (factoryMethodName != null) {
                return getTypeForFactoryBeanFromMethod(mbd.getBeanClass(), factoryMethodName);
            } else {
                return GenericTypeResolver.resolveTypeArgument(mbd.getBeanClass(), FactoryBean.class);
            }
        }

        return null;
    }

    /**
     * Introspect the factory method signatures on the given bean class,
     * trying to find a common {@code FactoryBean} object type declared there.
     *
     * @param beanClass         the bean class to find the factory method on
     * @param factoryMethodName the name of the factory method
     * @return the common {@code FactoryBean} object type, or {@code null} if none
     */
    private Class<?> getTypeForFactoryBeanFromMethod(Class<?> beanClass, final String factoryMethodName) {
        class Holder {
            Class<?> value = null;
        }
        final Holder objectType = new Holder();

        // CGLIB subclass methods hide generic parameters; look at the original user class.
        Class<?> fbClass = ClassUtils.getUserClass(beanClass);

        // Find the given factory method, taking into account that in the case of
        // @Bean methods, there may be parameters present.
        ReflectionUtils.doWithMethods(fbClass,
                new ReflectionUtils.MethodCallback() {
                    @Override
                    public void doWith(Method method) {
                        if (method.getName().equals(factoryMethodName) &&
                                FactoryBean.class.isAssignableFrom(method.getReturnType())) {
                            Class<?> currentType = GenericTypeResolver.resolveReturnTypeArgument(
                                    method, FactoryBean.class);
                            if (currentType != null) {
                                objectType.value = ClassUtils.determineCommonAncestor(currentType, objectType.value);
                            }
                        }
                    }
                });

        return (objectType.value != null && Object.class != objectType.value ? objectType.value : null);
    }

    /**
     * Obtain a reference for early access to the specified bean,
     * typically for the purpose of resolving a circular reference.
     *
     * @param beanName the name of the bean (for error handling purposes)
     * @param mbd      the merged bean definition for the bean
     * @param bean     the raw bean instance
     * @return the object to expose as bean reference
     */
    protected Object getEarlyBeanReference(String beanName, RootBeanDefinition mbd, Object bean) {
        Object exposedObject = bean;
        if (bean != null && !mbd.isSynthetic() && hasInstantiationAwareBeanPostProcessors()) {
            for (BeanPostProcessor bp : getBeanPostProcessors()) {
                if (bp instanceof SmartInstantiationAwareBeanPostProcessor) {
                    SmartInstantiationAwareBeanPostProcessor ibp = (SmartInstantiationAwareBeanPostProcessor) bp;
                    exposedObject = ibp.getEarlyBeanReference(exposedObject, beanName);
                    if (exposedObject == null) {
                        return null;
                    }
                }
            }
        }
        return exposedObject;
    }


    //---------------------------------------------------------------------
    // Implementation methods
    //---------------------------------------------------------------------

    /**
     * Obtain a "shortcut" singleton FactoryBean instance to use for a
     * {@code getObjectType()} call, without full initialization of the FactoryBean.
     *
     * @param beanName the name of the bean
     * @param mbd      the bean definition for the bean
     * @return the FactoryBean instance, or {@code null} to indicate
     * that we couldn't obtain a shortcut FactoryBean instance
     */
    private FactoryBean<?> getSingletonFactoryBeanForTypeCheck(String beanName, RootBeanDefinition mbd) {
        synchronized (getSingletonMutex()) {
            BeanWrapper bw = this.factoryBeanInstanceCache.get(beanName);
            if (bw != null) {
                return (FactoryBean<?>) bw.getWrappedInstance();
            }
            Object beanInstance = getSingleton(beanName, false);
            if (beanInstance instanceof FactoryBean) {
                return (FactoryBean<?>) beanInstance;
            }
            if (isSingletonCurrentlyInCreation(beanName) ||
                    (mbd.getFactoryBeanName() != null && isSingletonCurrentlyInCreation(mbd.getFactoryBeanName()))) {
                return null;
            }

            Object instance;
            try {
                // Mark this bean as currently in creation, even if just partially.
                beforeSingletonCreation(beanName);
                // Give BeanPostProcessors a chance to return a proxy instead of the target bean instance.
                instance = resolveBeforeInstantiation(beanName, mbd);
                if (instance == null) {
                    bw = createBeanInstance(beanName, mbd, null);
                    instance = bw.getWrappedInstance();
                }
            } finally {
                // Finished partial creation of this bean.
                afterSingletonCreation(beanName);
            }

            FactoryBean<?> fb = getFactoryBean(beanName, instance);
            if (bw != null) {
                this.factoryBeanInstanceCache.put(beanName, bw);
            }
            return fb;
        }
    }

    /**
     * Obtain a "shortcut" non-singleton FactoryBean instance to use for a
     * {@code getObjectType()} call, without full initialization of the FactoryBean.
     *
     * @param beanName the name of the bean
     * @param mbd      the bean definition for the bean
     * @return the FactoryBean instance, or {@code null} to indicate
     * that we couldn't obtain a shortcut FactoryBean instance
     */
    private FactoryBean<?> getNonSingletonFactoryBeanForTypeCheck(String beanName, RootBeanDefinition mbd) {
        if (isPrototypeCurrentlyInCreation(beanName)) {
            return null;
        }

        Object instance;
        try {
            // Mark this bean as currently in creation, even if just partially.
            beforePrototypeCreation(beanName);
            // Give BeanPostProcessors a chance to return a proxy instead of the target bean instance.
            instance = resolveBeforeInstantiation(beanName, mbd);
            if (instance == null) {
                BeanWrapper bw = createBeanInstance(beanName, mbd, null);
                instance = bw.getWrappedInstance();
            }
        } catch (BeanCreationException ex) {
            // Can only happen when getting a FactoryBean.
            if (logger.isDebugEnabled()) {
                logger.debug("Bean creation exception on non-singleton FactoryBean type check: " + ex);
            }
            onSuppressedException(ex);
            return null;
        } finally {
            // Finished partial creation of this bean.
            afterPrototypeCreation(beanName);
        }

        return getFactoryBean(beanName, instance);
    }

    /**
     * Apply MergedBeanDefinitionPostProcessors to the specified bean definition,
     * invoking their {@code postProcessMergedBeanDefinition} methods.
     *
     * @param mbd      the merged bean definition for the bean
     * @param beanType the actual type of the managed bean instance
     * @param beanName the name of the bean
     * @see MergedBeanDefinitionPostProcessor#postProcessMergedBeanDefinition
     */
    protected void applyMergedBeanDefinitionPostProcessors(RootBeanDefinition mbd, Class<?> beanType, String beanName) {
        for (BeanPostProcessor bp : getBeanPostProcessors()) {
            if (bp instanceof MergedBeanDefinitionPostProcessor) {
                MergedBeanDefinitionPostProcessor bdp = (MergedBeanDefinitionPostProcessor) bp;
                bdp.postProcessMergedBeanDefinition(mbd, beanType, beanName);
            }
        }
    }

    /**
     * Apply before-instantiation post-processors, resolving whether there is a
     * before-instantiation shortcut for the specified bean.
     * @param beanName the name of the bean
     * @param mbd the bean definition for the bean
     * @return the shortcut-determined bean instance, or {@code null} if none
     */
    /**
     * 在该方法中，当前置处理方法返回的 bean 不为空时，后置处理才会被执行。
     * 前置处理器是 InstantiationAwareBeanPostProcessor 类型的，
     * 该类型处理器一般用在 Spring 框架内部，比如 AOP 模块中的AbstractAutoProxyCreator
     * 抽象类间接实现了这个接口中的 postProcessBeforeInstantiation方法，所以 AOP 可以在这个方法中生成为目标类的代理对象。
     * 不过在调试的过程中，发现 AOP 在此处生成代理对象是有条件的。一般情况下条件都不成立，
     * 也就不会在此处生成代理对象。
     */
    protected Object resolveBeforeInstantiation(String beanName, RootBeanDefinition mbd) {
        Object bean = null;
        if (!Boolean.FALSE.equals(mbd.beforeInstantiationResolved)) {
            // Make sure bean class is actually resolved at this point.
            if (!mbd.isSynthetic() && hasInstantiationAwareBeanPostProcessors()) {
                Class<?> targetType = determineTargetType(beanName, mbd);
                if (targetType != null) {
                    /**
                     * 初始化前置处理
                     */
                    bean = applyBeanPostProcessorsBeforeInstantiation(targetType, beanName);
                    if (bean != null) {
                        /**
                         * 初始化后置处理
                         */
                        bean = applyBeanPostProcessorsAfterInitialization(bean, beanName);
                    }
                }
            }
            mbd.beforeInstantiationResolved = (bean != null);
        }
        return bean;
    }

    /**
     * Apply InstantiationAwareBeanPostProcessors to the specified bean definition
     * (by class and name), invoking their {@code postProcessBeforeInstantiation} methods.
     * <p>Any returned object will be used as the bean instead of actually instantiating
     * the target bean. A {@code null} return value from the post-processor will
     * result in the target bean being instantiated.
     *
     * @param beanClass the class of the bean to be instantiated
     * @param beanName  the name of the bean
     * @return the bean object to use instead of a default instance of the target bean, or {@code null}
     * @see InstantiationAwareBeanPostProcessor#postProcessBeforeInstantiation
     */
    protected Object applyBeanPostProcessorsBeforeInstantiation(Class<?> beanClass, String beanName) {
        for (BeanPostProcessor bp : getBeanPostProcessors()) {
            /**
             * InstantiationAwareBeanPostProcessor 一般在 Spring 框架内部使用，不建议用户直接使用
             */
            if (bp instanceof InstantiationAwareBeanPostProcessor) {
                InstantiationAwareBeanPostProcessor ibp = (InstantiationAwareBeanPostProcessor) bp;
                /**
                 *  bean 初始化前置处理
                 */
                Object result = ibp.postProcessBeforeInstantiation(beanClass, beanName);
                if (result != null) {
                    return result;
                }
            }
        }
        return null;
    }

    /**
     * Create a new instance for the specified bean, using an appropriate instantiation strategy:
     * factory method, constructor autowiring, or simple instantiation.
     * @param beanName the name of the bean
     * @param mbd the bean definition for the bean
     * @param args explicit arguments to use for constructor or factory method invocation
     * @return a BeanWrapper for the new instance
     * @see #instantiateUsingFactoryMethod
     * @see #autowireConstructor
     * @see #instantiateBean
     */
    /**
     * 该方法执行流程：
     * 1. 检测类的访问权限，若禁止访问，则抛出异常
     * 2. 若工厂方法不为空，则通过工厂方法构建 bean 对象，并返回结果
     * 3. 若构造方式已解析过，则走快捷路径构建 bean 对象，并返回结果
     * 4. 如第三步不满足，则通过组合条件决定使用哪种方式构建 bean 对象
     * 这里有三种构造 bean 对象的方式，如下：
     * 1. 通过“工厂方法”的方式构造 bean 对象
     * 2. 通过“构造方法自动注入”的方式构造 bean 对象
     * 3. 通过“默认构造方法”的方式构造 bean 对象
     */
    protected BeanWrapper createBeanInstance(String beanName, RootBeanDefinition mbd, Object[] args) {
        // Make sure bean class is actually resolved at this point.
        Class<?> beanClass = resolveBeanClass(mbd, beanName);
        /**
         *
         * 检测类的访问权限，默认情况下。对于非public的类是允许访问的
         * 若禁止访问，会抛出异常
         */
        if (beanClass != null && !Modifier.isPublic(beanClass.getModifiers()) && !mbd.isNonPublicAccessAllowed()) {
            throw new BeanCreationException(mbd.getResourceDescription(), beanName,
                    "Bean class isn't public, and non-public access not allowed: " + beanClass.getName());
        }
        /**
         * 如果工厂方法不为空，则通过工厂方法构建bean对象
         */
        if (mbd.getFactoryMethodName() != null) {
            /**
             * 通过"工厂方法"的方式创建bean对象
             */
            return instantiateUsingFactoryMethod(beanName, mbd, args);
        }

        // Shortcut when re-creating the same bean...
        /**
         * 当多次构建同一个bean时，可以使用此处的快捷路径，即无需要再次推断应该使用哪种方式构造实例，以提高效率。
         * 比如在多次构建同一个prototype类型的bean时，就可以走此处的捷径。这里的resolved 和 mbd.constructorArgumentsResolved
         * 将会在bean第一次实例化的过程中被设置
         */
        boolean resolved = false;
        boolean autowireNecessary = false;
        if (args == null) {
            synchronized (mbd.constructorArgumentLock) {
                if (mbd.resolvedConstructorOrFactoryMethod != null) {
                    resolved = true;
                    autowireNecessary = mbd.constructorArgumentsResolved;
                }
            }
        }
        if (resolved) {
            if (autowireNecessary) {
                /**
                 * 通过 "构造方法自动注入" 的方式构造 bean 对象
                 */
                return autowireConstructor(beanName, mbd, null, null);
            } else {
                /**
                 * 通过 "默认构造方法"的方法构造bean对象
                 */
                return instantiateBean(beanName, mbd);
            }
        }

        // Candidate constructors for autowiring?
        /**
         *  由后置处理器决定返回那些构造方法
         */
        Constructor<?>[] ctors = determineConstructorsFromBeanPostProcessors(beanClass, beanName);
        /**
         * 下面的条件分支条件用于判断使用什么方式构造bean实例，有两种方式－构造方法自动注入和默认构造方法。
         * 判断条件由4部分综合而成，如下：
         * 	条件1： ctors != null -> 后置处理器返回构造方法数组是否为空
         * 	条件2：mbd.getResolvedAutowireMode() == RootBeanDefinition.AUTOWIRE_CONSTRUCTOR  -> bean 配置中的 autowire 属性是否为 constructor
         *	条件3：mbd.hasConstructorArgumentValues()  -> constructorArgumentValues 是否存在元素，即 bean 配置文件中是否配置了 <construct-arg/>
         *  条件4：!ObjectUtils.isEmpty(args) -> args 数组是否存在元素，args 是由用户调用getBean(String name, Object... args) 传入的
         *
         *  上面4个条件，只要有一个为 true，就会通过构造方法自动注入的方式构造 bean 实例
         *
         */
        if (ctors != null || mbd.getResolvedAutowireMode() == AUTOWIRE_CONSTRUCTOR ||
                mbd.hasConstructorArgumentValues() || !ObjectUtils.isEmpty(args)) {
            /**
             * 通过"构造方法自动注入" 的方式构造bean对象
             */
            return autowireConstructor(beanName, mbd, ctors, args);
        }

        // No special handling: simply use no-arg constructor.
        /**
         * 通过"默认构造方法"的方式构造bean对象
         */
        return instantiateBean(beanName, mbd);
    }

    /**
     * Determine candidate constructors to use for the given bean, checking all registered
     * {@link SmartInstantiationAwareBeanPostProcessor SmartInstantiationAwareBeanPostProcessors}.
     *
     * @param beanClass the raw class of the bean
     * @param beanName  the name of the bean
     * @return the candidate constructors, or {@code null} if none specified
     * @throws org.springframework.beans.BeansException in case of errors
     * @see org.springframework.beans.factory.config.SmartInstantiationAwareBeanPostProcessor#determineCandidateConstructors
     */
    protected Constructor<?>[] determineConstructorsFromBeanPostProcessors(Class<?> beanClass, String beanName)
            throws BeansException {

        if (beanClass != null && hasInstantiationAwareBeanPostProcessors()) {
            for (BeanPostProcessor bp : getBeanPostProcessors()) {
                if (bp instanceof SmartInstantiationAwareBeanPostProcessor) {
                    SmartInstantiationAwareBeanPostProcessor ibp = (SmartInstantiationAwareBeanPostProcessor) bp;
                    Constructor<?>[] ctors = ibp.determineCandidateConstructors(beanClass, beanName);
                    if (ctors != null) {
                        return ctors;
                    }
                }
            }
        }
        return null;
    }

    /**
     * Instantiate the given bean using its default constructor.
     *
     * @param beanName the name of the bean
     * @param mbd      the bean definition for the bean
     * @return a BeanWrapper for the new instance
     */
    protected BeanWrapper instantiateBean(final String beanName, final RootBeanDefinition mbd) {
        try {
            Object beanInstance;
            final BeanFactory parent = this;
            /**
             * if 条件分支里的一大坨是 Java 安全相关代码，可以忽略，直接看else分支
             */
            if (System.getSecurityManager() != null) {
                beanInstance = AccessController.doPrivileged(new PrivilegedAction<Object>() {
                    @Override
                    public Object run() {
                        return getInstantiationStrategy().instantiate(mbd, beanName, parent);
                    }
                }, getAccessControlContext());
            } else {
                /**
                 * 调用实例化策略创建实例，默认情况下使用反射创建对象。如果bean的配置信息中
                 * 包含lookup－method 和 replace-method ,则通过 GGLIB 创建 bean 对象
                 */
                beanInstance = getInstantiationStrategy().instantiate(mbd, beanName, parent);
            }
            // 创建BeanWrapperImpl 对象
            BeanWrapper bw = new BeanWrapperImpl(beanInstance);
            initBeanWrapper(bw);
            return bw;
        } catch (Throwable ex) {
            throw new BeanCreationException(
                    mbd.getResourceDescription(), beanName, "Instantiation of bean failed", ex);
        }
    }

    /**
     * Instantiate the bean using a named factory method. The method may be static, if the
     * mbd parameter specifies a class, rather than a factoryBean, or an instance variable
     * on a factory object itself configured using Dependency Injection.
     *
     * @param beanName     the name of the bean
     * @param mbd          the bean definition for the bean
     * @param explicitArgs argument values passed in programmatically via the getBean method,
     *                     or {@code null} if none (-> use constructor argument values from bean definition)
     * @return a BeanWrapper for the new instance
     * @see #getBean(String, Object[])
     */
    protected BeanWrapper instantiateUsingFactoryMethod(
            String beanName, RootBeanDefinition mbd, Object[] explicitArgs) {

        return new ConstructorResolver(this).instantiateUsingFactoryMethod(beanName, mbd, explicitArgs);
    }

    /**
     * "autowire constructor" (with constructor arguments by type) behavior.
     * Also applied if explicit constructor argument values are specified,
     * matching all remaining arguments with beans from the bean factory.
     * <p>This corresponds to constructor injection: In this mode, a Spring
     * bean factory is able to host components that expect constructor-based
     * dependency resolution.
     *
     * @param beanName     the name of the bean
     * @param mbd          the bean definition for the bean
     * @param ctors        the chosen candidate constructors
     * @param explicitArgs argument values passed in programmatically via the getBean method,
     *                     or {@code null} if none (-> use constructor argument values from bean definition)
     * @return a BeanWrapper for the new instance
     */
    protected BeanWrapper autowireConstructor(
            String beanName, RootBeanDefinition mbd, Constructor<?>[] ctors, Object[] explicitArgs) {
        /**
         * 创建ConstructorResolver 对象，并调用其 autowireConstructor 方法
         */
        return new ConstructorResolver(this).autowireConstructor(beanName, mbd, ctors, explicitArgs);
    }

    /**
     * Populate the bean instance in the given BeanWrapper with the property values
     * from the bean definition.
     *
     * @param beanName the name of the bean
     * @param mbd      the bean definition for the bean
     * @param bw       the BeanWrapper with bean instance
     */
    /**
     * 该方法的执行流程
     *      1. 获取属性列表 pvs
     *      2. 在属性被填充到 bean 前，应用后置处理自定义属性填充
     *      3. 根据名称或类型解析相关依赖
     *      4. 再次应用后置处理，用于动态修改属性列表 pvs 的内容
     *      5. 将属性应用到 bean 对象中
     *
     */
    protected void populateBean(String beanName, RootBeanDefinition mbd, BeanWrapper bw) {
        /**
         * 获取属性列表
         */
        PropertyValues pvs = mbd.getPropertyValues();

        if (bw == null) {
            if (!pvs.isEmpty()) {
                throw new BeanCreationException(
                        mbd.getResourceDescription(), beanName, "Cannot apply property values to null instance");
            } else {
                // Skip property population phase for null instance.
                return;
            }
        }

        // Give any InstantiationAwareBeanPostProcessors the opportunity to modify the
        // state of the bean before properties are set. This can be used, for example,
        // to support styles of field injection.
        boolean continueWithPropertyPopulation = true;
        /**
         * 在属性被填充前，给InstantiationAwareBeanPostProcessor 类型的后置处理器一个修改bean状态的机会。关于这段后置引用，官方的解释是：
         * 让用户可以自定义属性注入。比如用户实现一个 InstantiationAwareBeanPostProcessor 类型的后置处理器，并通过 postProcessAfterInstantiation
         * 方法向bean的成员变量注入自定义的信息。当然，如果无特殊需求，直接使用配置中的信息注入即可。另外，spring并不建议大家直接实现InstantiationAwareBeanPostProcessor
         * 接口，如果想实现这种类型的后置处理器，更建议通过继承 InstantiationAwareBeanPostProcessorAdapter 抽象类实现自定义后置处理器
         */
        if (!mbd.isSynthetic() && hasInstantiationAwareBeanPostProcessors()) {
            for (BeanPostProcessor bp : getBeanPostProcessors()) {
                if (bp instanceof InstantiationAwareBeanPostProcessor) {
                    InstantiationAwareBeanPostProcessor ibp = (InstantiationAwareBeanPostProcessor) bp;
                    if (!ibp.postProcessAfterInstantiation(bw.getWrappedInstance(), beanName)) {
                        continueWithPropertyPopulation = false;
                        break;
                    }
                }
            }
        }
        /**
         *  如果上面设置 continueWithPropertyPopulation = false，表明用户可能已经自己填充了
         *  bean 的属性，不需要 Spring 帮忙填充了。此时直接返回即可
         */
        if (!continueWithPropertyPopulation) {
            return;
        }
        /**
         * 根据名称或类型注入依赖
         */
        if (mbd.getResolvedAutowireMode() == RootBeanDefinition.AUTOWIRE_BY_NAME ||
                mbd.getResolvedAutowireMode() == RootBeanDefinition.AUTOWIRE_BY_TYPE) {
            MutablePropertyValues newPvs = new MutablePropertyValues(pvs);

            // Add property values based on autowire by name if applicable.
            /**
             * 通过属性名称注入依赖
             */
            if (mbd.getResolvedAutowireMode() == RootBeanDefinition.AUTOWIRE_BY_NAME) {
                autowireByName(beanName, mbd, bw, newPvs);
            }

            // Add property values based on autowire by type if applicable.
            /**
             * 通过属性类型注入依赖
             */
            if (mbd.getResolvedAutowireMode() == RootBeanDefinition.AUTOWIRE_BY_TYPE) {
                autowireByType(beanName, mbd, bw, newPvs);
            }

            pvs = newPvs;
        }

        boolean hasInstAwareBpps = hasInstantiationAwareBeanPostProcessors();
        boolean needsDepCheck = (mbd.getDependencyCheck() != RootBeanDefinition.DEPENDENCY_CHECK_NONE);
        /**
         * 这里又是一种后置处理，用于在Spring 填充属性到bean对象前，对属性的值进行相应的处理，
         * 比如可以修改某些属性的值，这时注入到bean中的值就不是配置文件中的内容了，而是经过后置处理器修改后的内容
         */
        if (hasInstAwareBpps || needsDepCheck) {
            PropertyDescriptor[] filteredPds = filterPropertyDescriptorsForDependencyCheck(bw, mbd.allowCaching);
            if (hasInstAwareBpps) {
                for (BeanPostProcessor bp : getBeanPostProcessors()) {
                    if (bp instanceof InstantiationAwareBeanPostProcessor) {
                        InstantiationAwareBeanPostProcessor ibp = (InstantiationAwareBeanPostProcessor) bp;
                        // 对属性进行后置处理
                        pvs = ibp.postProcessPropertyValues(pvs, filteredPds, bw.getWrappedInstance(), beanName);
                        if (pvs == null) {
                            return;
                        }
                    }
                }
            }
            if (needsDepCheck) {
                checkDependencies(beanName, mbd, filteredPds, pvs);
            }
        }
        /**
         * 应用属性值到bean对象中
         */
        applyPropertyValues(beanName, mbd, bw, pvs);
    }

    /**
     * Fill in any missing property values with references to
     * other beans in this factory if autowire is set to "byName".
     *
     * @param beanName the name of the bean we're wiring up.
     *                 Useful for debugging messages; not used functionally.
     * @param mbd      bean definition to update through autowiring
     * @param bw       the BeanWrapper from which we can obtain information about the bean
     * @param pvs      the PropertyValues to register wired objects with
     */
    protected void autowireByName(
            String beanName, AbstractBeanDefinition mbd, BeanWrapper bw, MutablePropertyValues pvs) {
        /**
         * 获取非简单类型属性的名称，且该属性未被配置在配置文件中。这里从反面解释一下什么是"非简单类型"属性
         * 我们先来看看spring认为的"简单类型"属性有哪些，如下：
         *   1. CharSequence 接口的实现类，比如 String
         *   2. Enum
         *   3. Date
         *   4. URI/URL
         *   5. Number 的继承类，比如 Integer/Long
         *   6. byte/short/int... 等基本类型
         *   7. Locale
         *   8. 以上所有类型的数组形式，比如 String[]、Date[]、int[] 等等
         *   除了要求非简单类型的属性外，还要求属性未在配置文件中配置过，也就是pvs.contains(pd.getName()) = false
         */
        String[] propertyNames = unsatisfiedNonSimpleProperties(mbd, bw);
        for (String propertyName : propertyNames) {
            /**
             * 检测是否存在与propertyName 相关的bean 或 BeanDefinition。若存在，则调用BeanFactory.getBean 方法获取bean实例
             */
            if (containsBean(propertyName)) {
                /**
                 * 从容器获取相应的bean实例
                 */
                Object bean = getBean(propertyName);
                /**
                 * 将解析出bean 存入到属性值类别（pvs）中
                 */
                pvs.add(propertyName, bean);
                registerDependentBean(propertyName, beanName);
                if (logger.isDebugEnabled()) {
                    logger.debug("Added autowiring by name from bean name '" + beanName +
                            "' via property '" + propertyName + "' to bean named '" + propertyName + "'");
                }
            } else {
                if (logger.isTraceEnabled()) {
                    logger.trace("Not autowiring property '" + propertyName + "' of bean '" + beanName +
                            "' by name: no matching bean found");
                }
            }
        }
    }

    /**
     * Abstract method defining "autowire by type" (bean properties by type) behavior.
     * <p>This is like PicoContainer default, in which there must be exactly one bean
     * of the property type in the bean factory. This makes bean factories simple to
     * configure for small namespaces, but doesn't work as well as standard Spring
     * behavior for bigger applications.
     *
     * @param beanName the name of the bean to autowire by type
     * @param mbd      the merged bean definition to update through autowiring
     * @param bw       the BeanWrapper from which we can obtain information about the bean
     * @param pvs      the PropertyValues to register wired objects with
     */
    protected void autowireByType(
            String beanName, AbstractBeanDefinition mbd, BeanWrapper bw, MutablePropertyValues pvs) {

        TypeConverter converter = getCustomTypeConverter();
        if (converter == null) {
            converter = bw;
        }

        Set<String> autowiredBeanNames = new LinkedHashSet<String>(4);
        /**
         * 获取非简单类型的属性
         */
        String[] propertyNames = unsatisfiedNonSimpleProperties(mbd, bw);
        for (String propertyName : propertyNames) {
            try {
                PropertyDescriptor pd = bw.getPropertyDescriptor(propertyName);
                // Don't try autowiring by type for type Object: never makes sense,
                // even if it technically is a unsatisfied, non-simple property.
                /**
                 * 如果属性类型为Object，则忽略，不做解析
                 */
                if (Object.class != pd.getPropertyType()) {
                    /**
                     * 获取 setter 方法(write method) 的参数信息，比如参数在参数列表中的位置，参数类型，以及该参数所归属的方法等信息
                     */
                    MethodParameter methodParam = BeanUtils.getWriteMethodParameter(pd);
                    // Do not allow eager init for type matching in case of a prioritized post-processor.
                    boolean eager = !PriorityOrdered.class.isAssignableFrom(bw.getWrappedClass());
                    /**
                     * 创建依赖描述对象
                     */
                    DependencyDescriptor desc = new AutowireByTypeDependencyDescriptor(methodParam, eager);
                    /**
                     * 下面的方法用于解析依赖，过程比较复杂
                     */
                    Object autowiredArgument = resolveDependency(desc, beanName, autowiredBeanNames, converter);
                    if (autowiredArgument != null) {
                        /**
                         * 将解析出得bean存入到属性值列表（pvs） 中
                         */
                        pvs.add(propertyName, autowiredArgument);
                    }
                    for (String autowiredBeanName : autowiredBeanNames) {
                        registerDependentBean(autowiredBeanName, beanName);
                        if (logger.isDebugEnabled()) {
                            logger.debug("Autowiring by type from bean name '" + beanName + "' via property '" +
                                    propertyName + "' to bean named '" + autowiredBeanName + "'");
                        }
                    }
                    autowiredBeanNames.clear();
                }
            } catch (BeansException ex) {
                throw new UnsatisfiedDependencyException(mbd.getResourceDescription(), beanName, propertyName, ex);
            }
        }
    }


    /**
     * Return an array of non-simple bean properties that are unsatisfied.
     * These are probably unsatisfied references to other beans in the
     * factory. Does not include simple properties like primitives or Strings.
     *
     * @param mbd the merged bean definition the bean was created with
     * @param bw  the BeanWrapper the bean was created with
     * @return an array of bean property names
     * @see org.springframework.beans.BeanUtils#isSimpleProperty
     */
    protected String[] unsatisfiedNonSimpleProperties(AbstractBeanDefinition mbd, BeanWrapper bw) {
        Set<String> result = new TreeSet<String>();
        PropertyValues pvs = mbd.getPropertyValues();
        PropertyDescriptor[] pds = bw.getPropertyDescriptors();
        for (PropertyDescriptor pd : pds) {
            if (pd.getWriteMethod() != null && !isExcludedFromDependencyCheck(pd) && !pvs.contains(pd.getName()) &&
                    !BeanUtils.isSimpleProperty(pd.getPropertyType())) {
                result.add(pd.getName());
            }
        }
        return StringUtils.toStringArray(result);
    }

    /**
     * Extract a filtered set of PropertyDescriptors from the given BeanWrapper,
     * excluding ignored dependency types or properties defined on ignored dependency interfaces.
     *
     * @param bw    the BeanWrapper the bean was created with
     * @param cache whether to cache filtered PropertyDescriptors for the given bean Class
     * @return the filtered PropertyDescriptors
     * @see #isExcludedFromDependencyCheck
     * @see #filterPropertyDescriptorsForDependencyCheck(org.springframework.beans.BeanWrapper)
     */
    protected PropertyDescriptor[] filterPropertyDescriptorsForDependencyCheck(BeanWrapper bw, boolean cache) {
        PropertyDescriptor[] filtered = this.filteredPropertyDescriptorsCache.get(bw.getWrappedClass());
        if (filtered == null) {
            filtered = filterPropertyDescriptorsForDependencyCheck(bw);
            if (cache) {
                PropertyDescriptor[] existing =
                        this.filteredPropertyDescriptorsCache.putIfAbsent(bw.getWrappedClass(), filtered);
                if (existing != null) {
                    filtered = existing;
                }
            }
        }
        return filtered;
    }

    /**
     * Extract a filtered set of PropertyDescriptors from the given BeanWrapper,
     * excluding ignored dependency types or properties defined on ignored dependency interfaces.
     *
     * @param bw the BeanWrapper the bean was created with
     * @return the filtered PropertyDescriptors
     * @see #isExcludedFromDependencyCheck
     */
    protected PropertyDescriptor[] filterPropertyDescriptorsForDependencyCheck(BeanWrapper bw) {
        List<PropertyDescriptor> pds =
                new ArrayList<PropertyDescriptor>(Arrays.asList(bw.getPropertyDescriptors()));
        for (Iterator<PropertyDescriptor> it = pds.iterator(); it.hasNext(); ) {
            PropertyDescriptor pd = it.next();
            if (isExcludedFromDependencyCheck(pd)) {
                it.remove();
            }
        }
        return pds.toArray(new PropertyDescriptor[pds.size()]);
    }

    /**
     * Determine whether the given bean property is excluded from dependency checks.
     * <p>This implementation excludes properties defined by CGLIB and
     * properties whose type matches an ignored dependency type or which
     * are defined by an ignored dependency interface.
     *
     * @param pd the PropertyDescriptor of the bean property
     * @return whether the bean property is excluded
     * @see #ignoreDependencyType(Class)
     * @see #ignoreDependencyInterface(Class)
     */
    protected boolean isExcludedFromDependencyCheck(PropertyDescriptor pd) {
        return (AutowireUtils.isExcludedFromDependencyCheck(pd) ||
                this.ignoredDependencyTypes.contains(pd.getPropertyType()) ||
                AutowireUtils.isSetterDefinedInInterface(pd, this.ignoredDependencyInterfaces));
    }

    /**
     * Perform a dependency check that all properties exposed have been set,
     * if desired. Dependency checks can be objects (collaborating beans),
     * simple (primitives and String), or all (both).
     *
     * @param beanName the name of the bean
     * @param mbd      the merged bean definition the bean was created with
     * @param pds      the relevant property descriptors for the target bean
     * @param pvs      the property values to be applied to the bean
     * @see #isExcludedFromDependencyCheck(java.beans.PropertyDescriptor)
     */
    protected void checkDependencies(
            String beanName, AbstractBeanDefinition mbd, PropertyDescriptor[] pds, PropertyValues pvs)
            throws UnsatisfiedDependencyException {

        int dependencyCheck = mbd.getDependencyCheck();
        for (PropertyDescriptor pd : pds) {
            if (pd.getWriteMethod() != null && !pvs.contains(pd.getName())) {
                boolean isSimple = BeanUtils.isSimpleProperty(pd.getPropertyType());
                boolean unsatisfied = (dependencyCheck == RootBeanDefinition.DEPENDENCY_CHECK_ALL) ||
                        (isSimple && dependencyCheck == RootBeanDefinition.DEPENDENCY_CHECK_SIMPLE) ||
                        (!isSimple && dependencyCheck == RootBeanDefinition.DEPENDENCY_CHECK_OBJECTS);
                if (unsatisfied) {
                    throw new UnsatisfiedDependencyException(mbd.getResourceDescription(), beanName, pd.getName(),
                            "Set this property value or disable dependency checking for this bean.");
                }
            }
        }
    }

    /**
     * Apply the given property values, resolving any runtime references
     * to other beans in this bean factory. Must use deep copy, so we
     * don't permanently modify this property.
     *
     * @param beanName the bean name passed for better exception information
     * @param mbd      the merged bean definition
     * @param bw       the BeanWrapper wrapping the target object
     * @param pvs      the new property values
     */
    /**
     *  该方法执行流程：
     *      1. 检测属性值列表是否已转换过的，若转换过，则直接填充属性，无需再次转换
     *      2. 遍历属性值列表 pvs，解析原始值 originalValue，得到解析值 resolvedValue
     *      3. 对解析后的属性值 resolvedValue 进行类型转换
     *      4. 将类型转换后的属性值设置到 PropertyValue 对象中，并将 PropertyValue 对象存入 deepCopy 集合中
     *      5. 将 deepCopy 中的属性信息注入到 bean 对象中
     *
     */
    protected void applyPropertyValues(String beanName, BeanDefinition mbd, BeanWrapper bw, PropertyValues pvs) {
        if (pvs == null || pvs.isEmpty()) {
            return;
        }

        if (System.getSecurityManager() != null && bw instanceof BeanWrapperImpl) {
            ((BeanWrapperImpl) bw).setSecurityContext(getAccessControlContext());
        }

        MutablePropertyValues mpvs = null;
        List<PropertyValue> original;

        if (pvs instanceof MutablePropertyValues) {
            mpvs = (MutablePropertyValues) pvs;
            /**
             * 如果属性列表pvs被转换过，则直接返回即可
             */
            if (mpvs.isConverted()) {
                // Shortcut: use the pre-converted values as-is.
                try {
                    bw.setPropertyValues(mpvs);
                    return;
                } catch (BeansException ex) {
                    throw new BeanCreationException(
                            mbd.getResourceDescription(), beanName, "Error setting property values", ex);
                }
            }
            original = mpvs.getPropertyValueList();
        } else {
            original = Arrays.asList(pvs.getPropertyValues());
        }

        TypeConverter converter = getCustomTypeConverter();
        if (converter == null) {
            converter = bw;
        }
        BeanDefinitionValueResolver valueResolver = new BeanDefinitionValueResolver(this, beanName, mbd, converter);

        // Create a deep copy, resolving any references for values.
        List<PropertyValue> deepCopy = new ArrayList<PropertyValue>(original.size());
        boolean resolveNecessary = false;
        /**
         * 遍历属性列表
         */
        for (PropertyValue pv : original) {
            /**
             * 如果属性值被转换过，则就不需要再次转换
             */
            if (pv.isConverted()) {
                deepCopy.add(pv);
            } else {
                String propertyName = pv.getName();
                Object originalValue = pv.getValue();
                /**
                 * 解析属性值。举例说明，先看下面的配置：
                 *
                 *   <bean id="macbook" class="MacBookPro">
                 *       <property name="manufacturer" value="Apple"/>
                 *       <property name="width" value="280"/>
                 *       <property name="cpu" ref="cpu"/>
                 *       <property name="interface">
                 *           <list>
                 *               <value>USB</value>
                 *               <value>HDMI</value>
                 *               <value>Thunderbolt</value>
                 *           </list>
                 *       </property>
                 *   </bean>
                 *
                 * 上面是一款电脑的配置信息，每个 property 配置经过下面的方法解析后，返回如下结果：
                 *   propertyName = "manufacturer", resolvedValue = "Apple"
                 *   propertyName = "width", resolvedValue = "280"
                 *   propertyName = "cpu", resolvedValue = "CPU@1234"  注：resolvedValue 是一个对象
                 *   propertyName = "interface", resolvedValue = ["USB", "HDMI", "Thunderbolt"]
                 *
                 * 如上所示，resolveValueIfNecessary 会将 ref 解析为具体的对象，将 <list>
                 * 标签转换为 List 对象等。对于 int 类型的配置，这里并未做转换，所以
                 * width = "280"，还是字符串。除了解析上面几种类型，该方法还会解析 <set/>、
                 * <map/>、<array/> 等集合配置
                 */
                Object resolvedValue = valueResolver.resolveValueIfNecessary(pv, originalValue);
                Object convertedValue = resolvedValue;
                /**
                 * convertible 表示属性值是否可转换，由两个条件合成而来。第一个条件不难理解，解释
                 * 一下第二个条件。第二个条件用于检测 propertyName 是否是 nested 或者 indexed，
                 * 直接举例说明吧：
                 *
                 *   public class Room {
                 *       private Door door = new Door();
                 *   }
                 *
                 * room 对象里面包含了 door 对象，如果我们想向 door 对象中注入属性值，则可以这样配置：
                 *
                 *   <bean id="room" class="com.demo.Room">
                 *      <property name="door.width" value="123"/>
                 *   </bean>
                 *
                 * isNestedOrIndexedProperty 会根据 propertyName 中是否包含 . 或 [  返回
                 * true 和 false。包含则返回 true，否则返回 false。关于 nested 类型的属性，我
                 * 没在实践中用过，所以不知道上面举的例子是不是合理。若不合理，欢迎指正，也请多多指教。
                 * 关于 nested 类型的属性，大家还可以参考 Spring 的官方文档：
                 *     https://docs.spring.io/spring/docs/4.3.17.RELEASE/spring-framework-reference/htmlsingle/#beans-beans-conventions
                 */
                boolean convertible = bw.isWritableProperty(propertyName) &&
                        !PropertyAccessorUtils.isNestedOrIndexedProperty(propertyName);
                /**
                 * 对于一般的属性，convertible 通常为true
                 */
                if (convertible) {
                    /**
                     * 对属性值的类型进行转换，比如将String 类型的属性值"123" 转换为Integer 类型的123
                     */
                    convertedValue = convertForProperty(resolvedValue, propertyName, bw, converter);
                }
                // Possibly store converted value in merged bean definition,
                // in order to avoid re-conversion for every created bean instance.
                /**
                 * 如果 originalValue 是通过autowireByType 或 autowireByName 解析而来，
                 * 那么此处条件成立，即(resolvedValue == originalValue) = true
                 */
                if (resolvedValue == originalValue) {
                    if (convertible) {
                        /**
                         * 将 convertedValue 设置到pv中，后续再次创建同一个bean时，就无需再次进行转换了
                         */
                        pv.setConvertedValue(convertedValue);
                    }
                    deepCopy.add(pv);
                }
                /**
                 * 如果原始值originalValue 是 TypedStringValue ，且转换后的值convertedValue不是Collection或数组类型，则将转换后的值存入到pv中
                 */
                else if (convertible && originalValue instanceof TypedStringValue &&
                        !((TypedStringValue) originalValue).isDynamic() &&
                        !(convertedValue instanceof Collection || ObjectUtils.isArray(convertedValue))) {
                    pv.setConvertedValue(convertedValue);
                    deepCopy.add(pv);
                } else {
                    resolveNecessary = true;
                    deepCopy.add(new PropertyValue(pv, convertedValue));
                }
            }
        }
        if (mpvs != null && !resolveNecessary) {
            mpvs.setConverted();
        }

        // Set our (possibly massaged) deep copy.
        try {
            /**
             * 将所有的属性值设置到bean实例中
             */
            bw.setPropertyValues(new MutablePropertyValues(deepCopy));
        } catch (BeansException ex) {
            throw new BeanCreationException(
                    mbd.getResourceDescription(), beanName, "Error setting property values", ex);
        }
    }

    /**
     * Convert the given value for the specified target property.
     */
    private Object convertForProperty(Object value, String propertyName, BeanWrapper bw, TypeConverter converter) {
        if (converter instanceof BeanWrapperImpl) {
            return ((BeanWrapperImpl) converter).convertForProperty(value, propertyName);
        } else {
            PropertyDescriptor pd = bw.getPropertyDescriptor(propertyName);
            MethodParameter methodParam = BeanUtils.getWriteMethodParameter(pd);
            return converter.convertIfNecessary(value, pd.getPropertyType(), methodParam);
        }
    }


    /**
     * Initialize the given bean instance, applying factory callbacks
     * as well as init methods and bean post processors.
     * <p>Called from {@link #createBean} for traditionally defined beans,
     * and from {@link #initializeBean} for existing bean instances.
     *
     * @param beanName the bean name in the factory (for debugging purposes)
     * @param bean     the new bean instance we may need to initialize
     * @param mbd      the bean definition that the bean was created with
     *                 (can also be {@code null}, if given an existing bean instance)
     * @return the initialized bean instance (potentially wrapped)
     * @see BeanNameAware
     * @see BeanClassLoaderAware
     * @see BeanFactoryAware
     * @see #applyBeanPostProcessorsBeforeInitialization
     * @see #invokeInitMethods
     * @see #applyBeanPostProcessorsAfterInitialization
     */
    /**
     *      该方法执行流程：
     *          1. 检测 bean 是否实现了 *Aware 类型接口，若实现，则向 bean 中注入相应的对象
     *          2. 执行 bean 初始化前置操作
     *          3. 执行初始化操作
     *          4. 执行 bean 初始化后置操作
     *
     */
    protected Object initializeBean(final String beanName, final Object bean, RootBeanDefinition mbd) {
        if (System.getSecurityManager() != null) {
            AccessController.doPrivileged(new PrivilegedAction<Object>() {
                @Override
                public Object run() {
                    invokeAwareMethods(beanName, bean);
                    return null;
                }
            }, getAccessControlContext());
        } else {
            /**
             * 若 bean 实现了 BeanNameAware、BeanFactoryAware、BeanClassLoaderAware 等接口，则向 bean 中注入相关对象
             */
            invokeAwareMethods(beanName, bean);
        }

        Object wrappedBean = bean;
        if (mbd == null || !mbd.isSynthetic()) {
            /**
             * 执行 bean 初始化前置操作
             */
            wrappedBean = applyBeanPostProcessorsBeforeInitialization(wrappedBean, beanName);
        }

        try {
            /**
             * 调用初始化方法：
             * 1. 若 bean 实现了 InitializingBean 接口，则调用 afterPropertiesSet 方法
             * 2. 若用户配置了 bean 的 init-method 属性，则调用用户在配置中指定的方法
             */
            invokeInitMethods(beanName, wrappedBean, mbd);
        } catch (Throwable ex) {
            throw new BeanCreationException(
                    (mbd != null ? mbd.getResourceDescription() : null),
                    beanName, "Invocation of init method failed", ex);
        }
        if (mbd == null || !mbd.isSynthetic()) {
            /**
             * 执行 bean 初始化后置操作，AOP 会在此处向目标对象中织入切面逻辑
             */
            wrappedBean = applyBeanPostProcessorsAfterInitialization(wrappedBean, beanName);
        }
        return wrappedBean;
    }

    private void invokeAwareMethods(final String beanName, final Object bean) {
        if (bean instanceof Aware) {
            if (bean instanceof BeanNameAware) {
                /**
                 * 注入beanName字符串
                 */
                ((BeanNameAware) bean).setBeanName(beanName);
            }
            if (bean instanceof BeanClassLoaderAware) {
                /**
                 * 注入ClassLoader对象
                 */
                ((BeanClassLoaderAware) bean).setBeanClassLoader(getBeanClassLoader());
            }
            if (bean instanceof BeanFactoryAware) {
                /**
                 * 注入BeanFactory对象
                 */
                ((BeanFactoryAware) bean).setBeanFactory(AbstractAutowireCapableBeanFactory.this);
            }
        }
    }

    /**
     * Give a bean a chance to react now all its properties are set,
     * and a chance to know about its owning bean factory (this object).
     * This means checking whether the bean implements InitializingBean or defines
     * a custom init method, and invoking the necessary callback(s) if it does.
     *
     * @param beanName the bean name in the factory (for debugging purposes)
     * @param bean     the new bean instance we may need to initialize
     * @param mbd      the merged bean definition that the bean was created with
     *                 (can also be {@code null}, if given an existing bean instance)
     * @throws Throwable if thrown by init methods or by the invocation process
     * @see #invokeCustomInitMethod
     */
    protected void invokeInitMethods(String beanName, final Object bean, RootBeanDefinition mbd)
            throws Throwable {
        /**
         * 检测bean是否是InitializingBean 类型的
         */
        boolean isInitializingBean = (bean instanceof InitializingBean);
        if (isInitializingBean && (mbd == null || !mbd.isExternallyManagedInitMethod("afterPropertiesSet"))) {
            if (logger.isDebugEnabled()) {
                logger.debug("Invoking afterPropertiesSet() on bean with name '" + beanName + "'");
            }
            if (System.getSecurityManager() != null) {
                try {
                    AccessController.doPrivileged(new PrivilegedExceptionAction<Object>() {
                        @Override
                        public Object run() throws Exception {
                            ((InitializingBean) bean).afterPropertiesSet();
                            return null;
                        }
                    }, getAccessControlContext());
                } catch (PrivilegedActionException pae) {
                    throw pae.getException();
                }
            } else {
                /**
                 * 如果bean实现了InitializingBean，则调用afterPropertiesSet 方法执行初始化逻辑
                 */
                ((InitializingBean) bean).afterPropertiesSet();
            }
        }

        if (mbd != null) {
            String initMethodName = mbd.getInitMethodName();
            if (initMethodName != null && !(isInitializingBean && "afterPropertiesSet".equals(initMethodName)) &&
                    !mbd.isExternallyManagedInitMethod(initMethodName)) {
                /**
                 * 调用用户自定义的初始化方法
                 */
                invokeCustomInitMethod(beanName, bean, mbd);
            }
        }
    }

    /**
     * Invoke the specified custom init method on the given bean.
     * Called by invokeInitMethods.
     * <p>Can be overridden in subclasses for custom resolution of init
     * methods with arguments.
     *
     * @see #invokeInitMethods
     */
    protected void invokeCustomInitMethod(String beanName, final Object bean, RootBeanDefinition mbd)
            throws Throwable {

        String initMethodName = mbd.getInitMethodName();
        final Method initMethod = (mbd.isNonPublicAccessAllowed() ?
                BeanUtils.findMethod(bean.getClass(), initMethodName) :
                ClassUtils.getMethodIfAvailable(bean.getClass(), initMethodName));
        if (initMethod == null) {
            if (mbd.isEnforceInitMethod()) {
                throw new BeanDefinitionValidationException("Couldn't find an init method named '" +
                        initMethodName + "' on bean with name '" + beanName + "'");
            } else {
                if (logger.isDebugEnabled()) {
                    logger.debug("No default init method named '" + initMethodName +
                            "' found on bean with name '" + beanName + "'");
                }
                // Ignore non-existent default lifecycle methods.
                return;
            }
        }

        if (logger.isDebugEnabled()) {
            logger.debug("Invoking init method  '" + initMethodName + "' on bean with name '" + beanName + "'");
        }

        if (System.getSecurityManager() != null) {
            AccessController.doPrivileged(new PrivilegedExceptionAction<Object>() {
                @Override
                public Object run() throws Exception {
                    ReflectionUtils.makeAccessible(initMethod);
                    return null;
                }
            });
            try {
                AccessController.doPrivileged(new PrivilegedExceptionAction<Object>() {
                    @Override
                    public Object run() throws Exception {
                        initMethod.invoke(bean);
                        return null;
                    }
                }, getAccessControlContext());
            } catch (PrivilegedActionException pae) {
                InvocationTargetException ex = (InvocationTargetException) pae.getException();
                throw ex.getTargetException();
            }
        } else {
            try {
                ReflectionUtils.makeAccessible(initMethod);
                initMethod.invoke(bean);
            } catch (InvocationTargetException ex) {
                throw ex.getTargetException();
            }
        }
    }


    /**
     * Applies the {@code postProcessAfterInitialization} callback of all
     * registered BeanPostProcessors, giving them a chance to post-process the
     * object obtained from FactoryBeans (for example, to auto-proxy them).
     *
     * @see #applyBeanPostProcessorsAfterInitialization
     */
    @Override
    protected Object postProcessObjectFromFactoryBean(Object object, String beanName) {
        return applyBeanPostProcessorsAfterInitialization(object, beanName);
    }

    /**
     * Overridden to clear FactoryBean instance cache as well.
     */
    @Override
    protected void removeSingleton(String beanName) {
        synchronized (getSingletonMutex()) {
            super.removeSingleton(beanName);
            this.factoryBeanInstanceCache.remove(beanName);
        }
    }

    /**
     * Overridden to clear FactoryBean instance cache as well.
     */
    @Override
    protected void clearSingletonCache() {
        synchronized (getSingletonMutex()) {
            super.clearSingletonCache();
            this.factoryBeanInstanceCache.clear();
        }
    }


    /**
     * Special DependencyDescriptor variant for Spring's good old autowire="byType" mode.
     * Always optional; never considering the parameter name for choosing a primary candidate.
     */
    @SuppressWarnings("serial")
    private static class AutowireByTypeDependencyDescriptor extends DependencyDescriptor {

        public AutowireByTypeDependencyDescriptor(MethodParameter methodParameter, boolean eager) {
            super(methodParameter, false, eager);
        }

        @Override
        public String getDependencyName() {
            return null;
        }
    }

}
