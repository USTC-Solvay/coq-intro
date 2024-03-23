<script setup>
import { ref, onMounted, computed } from 'vue'
import lz from 'lz-string'
const props = defineProps({
  code: {
    type: String,
    required: true
  }
})

const replaceMap = {
  '∀': 'forall',
  '→': '->',
  '×': '*',
  '∧': '/\\',
  '∨': '\\/',
  '¬': '~',
  '⇒': '=>',
  '↔': '<->',
  '≠': '<>',
}

const code = computed(() => {
  let result = lz.decompressFromBase64(props.code)
  for (const [key, value] of Object.entries(replaceMap)) {
    result = result.replaceAll(key, value)
  }
  return result
})

const url = computed(() => {
  return `http://localhost:11451?code=${encodeURIComponent(code.value)}`
})

const style = computed(() => {
  const lineNum = code.value.split('\n').length
  return {
    width: '100%',
    height: `${lineNum * 20 + 30}px`,
  }
})

const loaded = ref(false)
onMounted(() => {
  setTimeout(() => {
    loaded.value = true
  }, 3000);
})
</script>

<template>
  <RenderWhen context="main">
    <iframe :src="url" frameborder="0" :style border="2 gray-900 rounded-lg" tabindex="-1" />
    <div data-waitfor=".loaded">
      <div class=".loaded" v-show="loaded"/>
    </div>
    <template #fallback>
      <pre :style="style" class="overflow-y-auto leading-[20px] text-[14.6px]">{{ code }}</pre>
    </template>
  </RenderWhen>
</template>
