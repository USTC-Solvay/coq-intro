import type { ShikiSetupReturn } from '@slidev/types'
import { defineShikiSetup } from '@slidev/types'
import CoqLang from './coq.json'

export default defineShikiSetup((): ShikiSetupReturn => {
  return {
    langs: [
      CoqLang,
      'c',
    ],
  } as any
})
