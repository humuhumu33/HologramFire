import React, { useState, useEffect } from 'react'
import { Sparkles, Code, Zap, Users, Globe, ArrowRight, Play, Star, TrendingUp, Shield } from 'lucide-react'

interface WelcomeScreenProps {
  onGetStarted: () => void
}

const WelcomeScreen: React.FC<WelcomeScreenProps> = ({ onGetStarted }) => {
  const [currentFeature, setCurrentFeature] = useState(0)
  
  const features = [
    { icon: <Zap className="w-6 h-6" />, title: "Lightning Fast", description: "Get to work in seconds, not minutes" },
    { icon: <Shield className="w-6 h-6" />, title: "Secure", description: "Enterprise-grade security built-in" },
    { icon: <TrendingUp className="w-6 h-6" />, title: "Scalable", description: "Grows with your projects" },
    { icon: <Star className="w-6 h-6" />, title: "Premium", description: "Professional-grade tools" }
  ]

  useEffect(() => {
    const interval = setInterval(() => {
      setCurrentFeature((prev) => (prev + 1) % features.length)
    }, 2000)
    return () => clearInterval(interval)
  }, [])

  return (
    <div className="min-h-screen flex items-center justify-center p-8 relative overflow-hidden">
      {/* Animated Background Elements */}
      <div className="absolute inset-0 overflow-hidden">
        <div className="absolute -top-40 -right-40 w-80 h-80 bg-firebase-blue/20 rounded-full blur-3xl animate-pulse"></div>
        <div className="absolute -bottom-40 -left-40 w-80 h-80 bg-firebase-green/20 rounded-full blur-3xl animate-pulse delay-1000"></div>
        <div className="absolute top-1/2 left-1/2 transform -translate-x-1/2 -translate-y-1/2 w-96 h-96 bg-firebase-orange/10 rounded-full blur-3xl animate-pulse delay-500"></div>
      </div>

      <div className="max-w-7xl w-full relative z-10">
        {/* Header */}
        <div className="text-center mb-20">
          <div className="flex items-center justify-center mb-8">
            <div className="w-20 h-20 bg-white/20 backdrop-blur-md rounded-3xl flex items-center justify-center mr-6 shadow-2xl">
              <Sparkles className="w-10 h-10 text-white" />
            </div>
            <div className="text-left">
              <h1 className="text-6xl font-bold text-white mb-2">Firebase Studio</h1>
              <p className="text-xl text-white/80">The Future of Development</p>
            </div>
          </div>
          
          <p className="text-2xl text-white/90 mb-12 max-w-3xl mx-auto leading-relaxed">
            The full stack AI workspace that feels like magic. Build backends, frontends, and mobile apps with the smoothness of Revolut Exchange.
          </p>
          
          <div className="flex items-center justify-center space-x-6 mb-12">
            <button
              onClick={onGetStarted}
              className="firebase-button-primary text-xl px-12 py-5 bg-white text-firebase-blue hover:bg-firebase-gray-50 flex items-center shadow-2xl hover:shadow-3xl transform hover:scale-105 transition-all duration-300"
            >
              <Play className="mr-3 w-6 h-6" />
              Start Building
              <ArrowRight className="ml-3 w-6 h-6" />
            </button>
            
            <button className="firebase-button-ghost text-xl px-8 py-5 text-white border-2 border-white/30 hover:border-white/50 hover:bg-white/10 flex items-center backdrop-blur-md">
              Watch Demo
            </button>
          </div>

          {/* Rotating Feature Highlight */}
          <div className="inline-flex items-center bg-white/10 backdrop-blur-md rounded-2xl px-6 py-4 border border-white/20">
            <div className="text-white mr-4">{features[currentFeature].icon}</div>
            <div className="text-left">
              <div className="text-white font-semibold">{features[currentFeature].title}</div>
              <div className="text-white/80 text-sm">{features[currentFeature].description}</div>
            </div>
          </div>
        </div>

        {/* Features Grid */}
        <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-8 mb-20">
          <ModernFeatureCard
            icon={<Zap className="w-8 h-8" />}
            title="Lightning Fast Setup"
            description="Get from idea to running app in under 60 seconds. Import from GitHub, GitLab, or start fresh with our AI-powered templates."
            gradient="from-firebase-blue to-firebase-green"
          />
          <ModernFeatureCard
            icon={<Sparkles className="w-8 h-8" />}
            title="AI-Powered Development"
            description="Build with Gemini AI integrated throughout. Code generation, debugging, testing, and documentation - all powered by advanced AI."
            gradient="from-firebase-green to-firebase-orange"
          />
          <ModernFeatureCard
            icon={<Users className="w-8 h-8" />}
            title="Real-time Collaboration"
            description="Share workspaces instantly. Live preview URLs, real-time editing, and seamless team collaboration built for modern development."
            gradient="from-firebase-orange to-firebase-red"
          />
          <ModernFeatureCard
            icon={<Code className="w-8 h-8" />}
            title="Full-Stack Testing"
            description="Test everything in one place. Frontend, backend, APIs, and databases - all with integrated debugging and performance monitoring."
            gradient="from-firebase-red to-firebase-blue"
          />
          <ModernFeatureCard
            icon={<Globe className="w-8 h-8" />}
            title="One-Click Deployment"
            description="Deploy to Firebase Hosting, Cloud Run, or any platform with a single click. Monitor performance and usage in real-time."
            gradient="from-firebase-blue to-firebase-green"
          />
          <ModernFeatureCard
            icon={<Shield className="w-8 h-8" />}
            title="Enterprise Security"
            description="Bank-grade security with Firebase Auth, encrypted data, and compliance-ready infrastructure. Your code is always safe."
            gradient="from-firebase-green to-firebase-orange"
          />
        </div>

        {/* Status Bar */}
        <div className="text-center">
          <div className="inline-flex items-center bg-white/10 backdrop-blur-md rounded-2xl px-8 py-4 border border-white/20 shadow-xl">
            <div className="w-3 h-3 bg-green-400 rounded-full mr-4 animate-pulse shadow-lg"></div>
            <span className="text-white/90 text-lg font-medium">Firebase Studio is live with unlimited workspaces during preview</span>
          </div>
        </div>
      </div>
    </div>
  )
}

interface ModernFeatureCardProps {
  icon: React.ReactNode
  title: string
  description: string
  gradient: string
}

const ModernFeatureCard: React.FC<ModernFeatureCardProps> = ({ icon, title, description, gradient }) => {
  return (
    <div className="group relative">
      <div className="absolute inset-0 bg-gradient-to-br opacity-0 group-hover:opacity-100 transition-opacity duration-500 rounded-3xl blur-xl" 
           style={{ background: `linear-gradient(135deg, var(--tw-gradient-stops))` }}>
      </div>
      <div className="relative glass-effect-strong rounded-3xl p-8 hover:bg-white/25 transition-all duration-500 border border-white/30 hover:border-white/50 shadow-xl hover:shadow-2xl transform hover:-translate-y-2">
        <div className={`w-16 h-16 bg-gradient-to-br ${gradient} rounded-2xl flex items-center justify-center mb-6 shadow-lg group-hover:scale-110 transition-transform duration-300`}>
          <div className="text-white">{icon}</div>
        </div>
        <h3 className="text-white font-bold text-xl mb-4 group-hover:text-white transition-colors duration-300">{title}</h3>
        <p className="text-white/80 text-base leading-relaxed group-hover:text-white/90 transition-colors duration-300">{description}</p>
      </div>
    </div>
  )
}

export default WelcomeScreen
