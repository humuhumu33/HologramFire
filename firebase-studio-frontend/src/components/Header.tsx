import React, { useState } from 'react'
import { Menu, Sparkles, Settings, User, Bell, Search, Command, Zap, Globe } from 'lucide-react'

const Header: React.FC = () => {
  const [isSearchFocused, setIsSearchFocused] = useState(false)

  return (
    <header className="bg-white/80 backdrop-blur-md border-b border-firebase-gray-200/50 px-6 py-4 flex items-center justify-between sticky top-0 z-40">
      {/* Left Section */}
      <div className="flex items-center space-x-6">
        <button 
          className="p-2 hover:bg-firebase-gray-100 rounded-xl transition-all duration-200 hover:scale-105"
          aria-label="Toggle menu"
        >
          <Menu className="w-5 h-5 text-firebase-gray-600" />
        </button>
        
        <div className="flex items-center space-x-3">
          <div className="w-10 h-10 bg-gradient-to-br from-firebase-blue to-firebase-green rounded-xl flex items-center justify-center shadow-lg">
            <Sparkles className="w-6 h-6 text-white" />
          </div>
          <div className="flex flex-col">
            <span className="font-bold text-firebase-gray-900 text-lg">Firebase Studio</span>
            <span className="text-xs text-firebase-gray-500">AI Workspace</span>
          </div>
        </div>
      </div>

      {/* Center Section - Enhanced Search */}
      <div className="flex-1 max-w-2xl mx-8">
        <div className="relative group">
          <div className={`absolute inset-0 bg-gradient-to-r from-firebase-blue/20 to-firebase-green/20 rounded-2xl blur opacity-0 group-hover:opacity-100 transition-opacity duration-300 ${isSearchFocused ? 'opacity-100' : ''}`}></div>
          <div className="relative">
            <Search className="absolute left-4 top-1/2 transform -translate-y-1/2 w-5 h-5 text-firebase-gray-400 transition-colors duration-200" />
            <input
              type="text"
              placeholder="Search projects, files, or commands..."
              className="w-full pl-12 pr-16 py-3 bg-firebase-gray-50/80 border border-firebase-gray-200 rounded-2xl focus:outline-none focus:ring-2 focus:ring-firebase-blue/50 focus:border-transparent transition-all duration-200 placeholder-firebase-gray-400 backdrop-blur-sm"
              onFocus={() => setIsSearchFocused(true)}
              onBlur={() => setIsSearchFocused(false)}
            />
            <div className="absolute right-3 top-1/2 transform -translate-y-1/2 flex items-center space-x-1">
              <kbd className="px-2 py-1 text-xs bg-firebase-gray-200 text-firebase-gray-600 rounded-md">⌘</kbd>
              <kbd className="px-2 py-1 text-xs bg-firebase-gray-200 text-firebase-gray-600 rounded-md">K</kbd>
            </div>
          </div>
        </div>
      </div>

      {/* Right Section */}
      <div className="flex items-center space-x-3">
        {/* Quick Actions */}
        <div className="flex items-center space-x-2">
          <button 
            className="p-2 hover:bg-firebase-gray-100 rounded-xl transition-all duration-200 hover:scale-105 relative group"
            aria-label="Quick Deploy"
            title="Quick Deploy"
          >
            <Zap className="w-5 h-5 text-firebase-gray-600 group-hover:text-firebase-orange transition-colors" />
          </button>
          
          <button 
            className="p-2 hover:bg-firebase-gray-100 rounded-xl transition-all duration-200 hover:scale-105 relative group"
            aria-label="Live Preview"
            title="Live Preview"
          >
            <Globe className="w-5 h-5 text-firebase-gray-600 group-hover:text-firebase-green transition-colors" />
          </button>
        </div>

        {/* Notifications */}
        <button 
          className="p-2 hover:bg-firebase-gray-100 rounded-xl transition-all duration-200 hover:scale-105 relative group"
          aria-label="Notifications"
        >
          <Bell className="w-5 h-5 text-firebase-gray-600 group-hover:text-firebase-blue transition-colors" />
          <span className="absolute -top-1 -right-1 w-3 h-3 bg-firebase-red rounded-full animate-pulse"></span>
        </button>
        
        {/* Settings */}
        <button 
          className="p-2 hover:bg-firebase-gray-100 rounded-xl transition-all duration-200 hover:scale-105 group"
          aria-label="Settings"
        >
          <Settings className="w-5 h-5 text-firebase-gray-600 group-hover:text-firebase-gray-900 transition-colors" />
        </button>
        
        {/* User Profile */}
        <div className="flex items-center space-x-3 pl-3 border-l border-firebase-gray-200">
          <div className="flex flex-col items-end">
            <span className="text-sm font-medium text-firebase-gray-900">Developer</span>
            <span className="text-xs text-firebase-gray-500">Free Plan</span>
          </div>
          <div className="w-10 h-10 bg-gradient-to-br from-firebase-blue to-firebase-green rounded-xl flex items-center justify-center shadow-lg hover:shadow-xl transition-all duration-200 hover:scale-105 cursor-pointer">
            <User className="w-5 h-5 text-white" />
          </div>
        </div>
      </div>
    </header>
  )
}

export default Header
