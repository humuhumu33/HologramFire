import React, { useState, useEffect, Suspense } from 'react'
import Header from './components/Header'
import WelcomeScreen from './components/WelcomeScreen'
import StatusBar from './components/StatusBar'
import { WorkspaceProvider } from './contexts/WorkspaceContext'
import { LazyWrapper, preloadComponents } from './components/LazyWrapper'

// Lazy load the Workspace component
const LazyWorkspace = React.lazy(() => import('./components/Workspace'))

function App() {
  const [showWelcome, setShowWelcome] = useState(true)
  const [isTransitioning, setIsTransitioning] = useState(false)

  // Preload components when user interacts with welcome screen
  useEffect(() => {
    const timer = setTimeout(() => {
      preloadComponents()
    }, 2000) // Preload after 2 seconds

    return () => clearTimeout(timer)
  }, [])

  const handleGetStarted = () => {
    setIsTransitioning(true)
    
    // Add a smooth transition delay
    setTimeout(() => {
      setShowWelcome(false)
      setIsTransitioning(false)
    }, 300)
  }

  if (showWelcome) {
    return (
      <div className={`min-h-screen bg-gradient-to-br from-firebase-blue via-firebase-green to-firebase-orange transition-all duration-500 ${isTransitioning ? 'opacity-0 scale-95' : 'opacity-100 scale-100'}`}>
        <WelcomeScreen onGetStarted={handleGetStarted} />
      </div>
    )
  }

  return (
    <WorkspaceProvider>
      <div className="min-h-screen bg-firebase-gray-50 flex flex-col page-transition">
        <Header />
        <LazyWrapper
          fallback={
            <div className="flex-1 flex items-center justify-center">
              <div className="flex flex-col items-center space-y-4">
                <div className="w-12 h-12 border-4 border-firebase-blue border-t-transparent rounded-full animate-spin"></div>
                <p className="text-firebase-gray-600 text-lg font-medium">Loading Workspace...</p>
                <p className="text-firebase-gray-500 text-sm">Preparing your development environment</p>
              </div>
            </div>
          }
        >
          <Suspense fallback={
            <div className="flex-1 flex items-center justify-center">
              <div className="flex flex-col items-center space-y-4">
                <div className="w-8 h-8 border-4 border-firebase-blue border-t-transparent rounded-full animate-spin"></div>
                <p className="text-firebase-gray-600">Loading components...</p>
              </div>
            </div>
          }>
            <LazyWorkspace />
          </Suspense>
        </LazyWrapper>
        <StatusBar />
      </div>
    </WorkspaceProvider>
  )
}

export default App
