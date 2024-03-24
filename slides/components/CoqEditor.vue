<script setup>
import { useNav, useSlideContext } from "@slidev/client";
import lz from "lz-string";
import { computed } from "vue";

const props = defineProps({
  code: {
    type: String,
    required: true,
  },
});

const { isPrintMode, currentPage } = useNav();
const { $renderContext, $page } = useSlideContext();

const replaceMap = {
  "∀": "forall",
  "→": "->",
  "×": "*",
  "∧": "/\\",
  "∨": "\\/",
  "¬": "~",
  "⇒": "=>",
  "↔": "<->",
  "≠": "<>",
};

const code = computed(() => {
  let result = lz.decompressFromBase64(props.code);
  for (const [key, value] of Object.entries(replaceMap)) {
    result = result.replaceAll(key, value);
  }
  return result;
});

const url = computed(() => {
  return __DEV__
    ? `http://localhost:11451?code=${encodeURIComponent(code.value)}`
    : `${import.meta.env.BASE_URL}editor?code=${encodeURIComponent(code.value)}`;
});

const style = computed(() => {
  const lineNum = code.value.split("\n").length;
  return {
    width: "100%",
    height: `${lineNum * 20 + 30}px`,
  };
});

const editable = computed(() => {
  return (
    ["slide", "presenter"].includes($renderContext.value) &&
    !isPrintMode.value &&
    Math.abs(currentPage.value - $page.value) < 2
  );
});
</script>

<template>
  <iframe
    v-if="editable"
    :src="url"
    frameborder="0"
    :style
    border="2 gray-900 rounded-lg"
    tabindex="-1"
  />
  <pre
    v-else
    :style="style"
    class="overflow-y-auto leading-[20px] text-[14.6px]"
    >{{ code }}</pre
  >
</template>
