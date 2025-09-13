import React from 'react'
import { 
  Wifi, 
  WifiOff, 
  GitBranch, 
  CheckCircle, 
  AlertCircle, 
  Clock,
  Activity
} from 'lucide-react'

const StatusBar: React.FC = () => {
  const [isOnline, setIsOnline] = React.useState(navigator.onLine)
  const [currentTime, setCurrentTime] = React.useState(new Date())

  React.useEffect(() => {
    const handleOnline = () => setIsOnline(true)
    const handleOffline = () => setIsOnline(false)
    
    window.addEventListener('online', handleOnline)
    window.addEventListener('offline', handleOffline)
    
    const timer = setInterval(() => {
      setCurrentTime(new Date())
    }, 1000)

    return () => {
      window.removeEventListener('online', handleOnline)
      window.removeEventListener('offline', handleOffline)
      clearInterval(timer)
    }
  }, [])

  const formatTime = (date: Date) => {
    return date.toLocaleTimeString('en-US', { 
      hour12: false,
      hour: '2-digit',
      minute: '2-digit',
      second: '2-digit'
    })
  }

  return (
    <div className="h-6 bg-firebase-gray-800 text-firebase-gray-200 text-xs flex items-center justify-between px-4">
      <div className="flex items-center space-x-4">
        <div className="flex items-center space-x-1">
          <GitBranch className="w-3 h-3" />
          <span>main</span>
        </div>
        
        <div className="flex items-center space-x-1">
          <CheckCircle className="w-3 h-3 text-firebase-green" />
          <span>Ready</span>
        </div>
        
        <div className="flex items-center space-x-1">
          <Activity className="w-3 h-3 text-firebase-blue" />
          <span>TypeScript</span>
        </div>
      </div>

      <div className="flex items-center space-x-4">
        <div className="flex items-center space-x-1">
          {isOnline ? (
            <Wifi className="w-3 h-3 text-firebase-green" />
          ) : (
            <WifiOff className="w-3 h-3 text-firebase-red" />
          )}
          <span>{isOnline ? 'Online' : 'Offline'}</span>
        </div>
        
        <div className="flex items-center space-x-1">
          <Clock className="w-3 h-3" />
          <span>{formatTime(currentTime)}</span>
        </div>
      </div>
    </div>
  )
}

export default StatusBar
