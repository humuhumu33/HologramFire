import React, { useState, useRef, useEffect } from 'react'
import { 
  Monitor, 
  Smartphone, 
  Tablet, 
  RefreshCw, 
  ExternalLink, 
  Settings,
  Play,
  Square,
  Maximize2,
  Minimize2
} from 'lucide-react'

const PreviewPanel: React.FC = () => {
  const [device, setDevice] = useState<'desktop' | 'tablet' | 'mobile'>('desktop')
  const [isRunning, setIsRunning] = useState(false)
  const [isFullscreen, setIsFullscreen] = useState(false)
  const [previewUrl, setPreviewUrl] = useState('')
  const iframeRef = useRef<HTMLIFrameElement>(null)

  const deviceSizes = {
    desktop: { width: '100%', height: '100%' },
    tablet: { width: '768px', height: '1024px' },
    mobile: { width: '375px', height: '667px' }
  }

  const handleRefresh = () => {
    if (iframeRef.current) {
      iframeRef.current.src = iframeRef.current.src
    }
  }

  const handleRun = () => {
    setIsRunning(true)
    // Simulate starting the development server
    setTimeout(() => {
      setPreviewUrl('http://localhost:3000')
      setIsRunning(false)
    }, 2000)
  }

  const handleStop = () => {
    setIsRunning(false)
    setPreviewUrl('')
  }

  const handleFullscreen = () => {
    setIsFullscreen(!isFullscreen)
  }

  const handleOpenExternal = () => {
    if (previewUrl) {
      window.open(previewUrl, '_blank')
    }
  }

  return (
    <div className="h-full flex flex-col">
      {/* Header */}
      <div className="p-3 border-b border-firebase-gray-200 bg-white">
        <div className="flex items-center justify-between">
          <div className="flex items-center space-x-2">
            <Monitor className="w-4 h-4 text-firebase-gray-600" />
            <h3 className="font-semibold text-firebase-gray-900">Preview</h3>
          </div>
          
          <div className="flex items-center space-x-1">
            {/* Device Selector */}
            <div className="flex items-center bg-firebase-gray-100 rounded-lg p-1">
              <button
                onClick={() => setDevice('desktop')}
                className={`p-1 rounded ${
                  device === 'desktop' 
                    ? 'bg-white shadow-sm' 
                    : 'hover:bg-firebase-gray-200'
                }`}
                title="Desktop"
              >
                <Monitor className="w-4 h-4 text-firebase-gray-600" />
              </button>
              <button
                onClick={() => setDevice('tablet')}
                className={`p-1 rounded ${
                  device === 'tablet' 
                    ? 'bg-white shadow-sm' 
                    : 'hover:bg-firebase-gray-200'
                }`}
                title="Tablet"
              >
                <Tablet className="w-4 h-4 text-firebase-gray-600" />
              </button>
              <button
                onClick={() => setDevice('mobile')}
                className={`p-1 rounded ${
                  device === 'mobile' 
                    ? 'bg-white shadow-sm' 
                    : 'hover:bg-firebase-gray-200'
                }`}
                title="Mobile"
              >
                <Smartphone className="w-4 h-4 text-firebase-gray-600" />
              </button>
            </div>

            {/* Controls */}
            <div className="flex items-center space-x-1 ml-2">
              {!isRunning && !previewUrl ? (
                <button
                  onClick={handleRun}
                  className="p-1 hover:bg-firebase-gray-100 rounded"
                  title="Start Preview"
                >
                  <Play className="w-4 h-4 text-firebase-green" />
                </button>
              ) : (
                <button
                  onClick={handleStop}
                  className="p-1 hover:bg-firebase-gray-100 rounded"
                  title="Stop Preview"
                >
                  <Square className="w-4 h-4 text-firebase-red" />
                </button>
              )}
              
              <button
                onClick={handleRefresh}
                className="p-1 hover:bg-firebase-gray-100 rounded"
                title="Refresh"
                disabled={!previewUrl}
              >
                <RefreshCw className="w-4 h-4 text-firebase-gray-600" />
              </button>
              
              <button
                onClick={handleOpenExternal}
                className="p-1 hover:bg-firebase-gray-100 rounded"
                title="Open in New Tab"
                disabled={!previewUrl}
              >
                <ExternalLink className="w-4 h-4 text-firebase-gray-600" />
              </button>
              
              <button
                onClick={handleFullscreen}
                className="p-1 hover:bg-firebase-gray-100 rounded"
                title="Toggle Fullscreen"
              >
                {isFullscreen ? (
                  <Minimize2 className="w-4 h-4 text-firebase-gray-600" />
                ) : (
                  <Maximize2 className="w-4 h-4 text-firebase-gray-600" />
                )}
              </button>
            </div>
          </div>
        </div>
      </div>

      {/* Preview Content */}
      <div className="flex-1 bg-firebase-gray-100 p-4 overflow-hidden">
        {isRunning ? (
          <div className="h-full flex items-center justify-center">
            <div className="text-center">
              <div className="w-16 h-16 bg-firebase-blue/10 rounded-full flex items-center justify-center mx-auto mb-4">
                <RefreshCw className="w-8 h-8 text-firebase-blue animate-spin" />
              </div>
              <h3 className="text-lg font-medium text-firebase-gray-900 mb-2">
                Starting Preview Server...
              </h3>
              <p className="text-firebase-gray-500">
                This may take a few moments
              </p>
            </div>
          </div>
        ) : previewUrl ? (
          <div className="h-full flex items-center justify-center">
            <div 
              className="bg-white rounded-lg shadow-lg overflow-hidden"
              style={deviceSizes[device]}
            >
              <iframe
                ref={iframeRef}
                src={previewUrl}
                className="w-full h-full border-0"
                title="Preview"
              />
            </div>
          </div>
        ) : (
          <div className="h-full flex items-center justify-center">
            <div className="text-center max-w-md">
              <div className="w-20 h-20 bg-firebase-gray-200 rounded-2xl flex items-center justify-center mx-auto mb-6">
                <Monitor className="w-10 h-10 text-firebase-gray-400" />
              </div>
              <h3 className="text-xl font-semibold text-firebase-gray-900 mb-3">
                Live Preview
              </h3>
              <p className="text-firebase-gray-600 mb-6">
                Start the preview server to see your app running in real-time. 
                Changes to your code will be reflected instantly.
              </p>
              <button
                onClick={handleRun}
                className="firebase-button-primary flex items-center space-x-2 mx-auto"
              >
                <Play className="w-4 h-4" />
                <span>Start Preview</span>
              </button>
            </div>
          </div>
        )}
      </div>

      {/* Status Bar */}
      <div className="px-3 py-2 border-t border-firebase-gray-200 bg-firebase-gray-50">
        <div className="flex items-center justify-between text-xs text-firebase-gray-500">
          <div className="flex items-center space-x-4">
            <span>Device: {device}</span>
            {previewUrl && (
              <span>URL: {previewUrl}</span>
            )}
          </div>
          <div className="flex items-center space-x-2">
            {isRunning && (
              <div className="flex items-center space-x-1">
                <div className="w-2 h-2 bg-firebase-green rounded-full animate-pulse"></div>
                <span>Running</span>
              </div>
            )}
            {previewUrl && !isRunning && (
              <div className="flex items-center space-x-1">
                <div className="w-2 h-2 bg-firebase-blue rounded-full"></div>
                <span>Ready</span>
              </div>
            )}
          </div>
        </div>
      </div>
    </div>
  )
}

export default PreviewPanel
