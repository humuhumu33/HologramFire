import React, { Suspense, lazy, ComponentType } from 'react'

interface LazyWrapperProps {
  fallback?: React.ReactNode
  children: React.ReactNode
}

const DefaultFallback = () => (
  <div className="flex items-center justify-center h-64">
    <div className="flex flex-col items-center space-y-4">
      <div className="w-8 h-8 border-4 border-firebase-blue border-t-transparent rounded-full animate-spin"></div>
      <p className="text-firebase-gray-600 text-sm">Loading...</p>
    </div>
  </div>
)

export const LazyWrapper: React.FC<LazyWrapperProps> = ({ 
  fallback = <DefaultFallback />, 
  children 
}) => {
  return (
    <Suspense fallback={fallback}>
      {children}
    </Suspense>
  )
}

// Higher-order component for lazy loading
export function withLazyLoading<T extends object>(
  Component: ComponentType<T>,
  fallback?: React.ReactNode
) {
  return function LazyComponent(props: T) {
    return (
      <LazyWrapper fallback={fallback}>
        <Component {...props} />
      </LazyWrapper>
    )
  }
}

// Lazy load heavy components
export const LazyCodeEditor = lazy(() => import('./CodeEditor'))
export const LazyAIPanel = lazy(() => import('./AIPanel'))
export const LazyPreviewPanel = lazy(() => import('./PreviewPanel'))
export const LazyFileExplorer = lazy(() => import('./FileExplorer'))

// Preload components for better performance
export const preloadComponents = () => {
  import('./CodeEditor')
  import('./AIPanel')
  import('./PreviewPanel')
  import('./FileExplorer')
}
