import type { ShikiSetupReturn } from '@slidev/types'
import { defineShikiSetup } from '@slidev/types'
import CoqLang from './coq.json'
import Theme from './theme.json'

export default defineShikiSetup((): ShikiSetupReturn => {
  return {
    langs: [
      CoqLang as any,
      'cpp',
    ],
    theme: Theme as any,
  }
})
