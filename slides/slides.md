---
theme: seriph
background: cover.jpg
title: The Coq Proof Assistant
transition: slide-left
mdc: true
class: pt-0
---

# [The]{.op80} [Coq]{.font-mono.op100} [Proof Assistant]{.op80}

计算机辅助证明简介{.!op90}

---

# Preface

什么是计算机辅助证明

### 四色定理

- 1976 年，借助计算机验证了“1936个构形都是可约构形”的结论，从而证明了四色定理
- 2004 年，Georges Gonthier 使用 Coq **可靠地**证明了该结论

<v-click>

穷举法？ {.text-3xl.p-7}

</v-click>


<v-click>

不仅仅是！ {.text-3xl.p-7}

</v-click>

---

# Preface

### 用途

- 证明需要进行大量穷举的数学定理
- 使用真正严谨、没有歧义的语言进行数学证明
- 证明软件的正确性
  - 验证编译器的优化是否不改变程序的行为
  - 验证算法的正确性
- ...

---

# Preface

### 涉及

- 构建证明逻辑
- 函数式编程
- 类型理论

---

# 从枚举类型开始

看起来用处不大？

```coq
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
```

**Inductive**: 归纳

---

# 从枚举类型开始

函数 / 映射 / “定义”

```coq
Definition next_weekday (d:day) : day :=
  match d with
  | monday ⇒ tuesday
  | tuesday ⇒ wednesday
  | wednesday ⇒ thursday
  | thursday ⇒ friday
  | friday ⇒ monday
  | saturday ⇒ monday
  | sunday ⇒ monday
  end.
```

类型！

---

# 从枚举类型开始

从枚举开始的数据表示法：布尔值

```coq
Inductive bool : Type :=
  | true
  | false.
```

<div h-2 />

```coq
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ true
  | false ⇒ b2
  end.
```

---

# 从枚举类型开始

从枚举开始的数据表示法：自然数，基于皮亚诺公理

```coq
Inductive nat : Type :=
  | O
  | S (n : nat).  (* S 是 successor 的缩写 *)
```

<v-click>
<div>

| 十进制 | as `nat` |
| --- | --- |
| 0 | `O` |
| 1 | `S O` |
| 2 | `S (S O)` |
| 3 | `S (S (S O))` |

</div>
</v-click>

<div v-click class="text-3xl -mt-4 ml-10 font-serif -rotate-7">
一进制 ？？？
</div>

---

#### succ 的反操作：pred

```coq
Definition pred (n : nat) : nat :=
  match n with
  | O ⇒ O
  | S n' ⇒ n'
  end.
```

<div v-click class="text-xl mt-10">

如何判断奇偶性？

$\text{even:} \space \space \mathbb{N} \to \mathbb{B}$

</div>

---

# 递归函数

函数式编程的特征之一

#### even

```coq
Fixpoint even (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ even n'
  end.
```

#### odd

```coq
Definition odd (n:nat) : bool :=
  negb (even n).
```

---

# 递归函数

更多的例子

#### add

```coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O ⇒ m
  | S n' ⇒ S (plus n' m)
  end.
```

<div h-3 />

#### mult

```coq
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O ⇒ O
  | S n' ⇒ plus m (mult n' m)
  end.
```

---

# 好了，开始证吧！

从显然的命题开始

<!-- Should be interactive -->

$$
\forall n \in \N, \space 0 + n = n
$$

```coq
Theorem plus_O_n : ∀ n : nat, 0 + n = n.
```

```coq {hide|all}
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.
```

<div v-click pt-2>

*simpl* 简化表达式: $0 + n$ 由 $\text{add}$ 的定义，化简为 $n$

*reflexivity* 自反性: $a = a$ 必然成立！

</div>

---

# 通过改写证明

The `rewrite` tactic

$$
\forall n \in \N, \space n = m \Rightarrow n + n = m + m
$$

```coq
Theorem plus_id_example : ∀ n m:nat,
  n = m →
  n + n = m + m.
```

```coq {hide|3}{finally:'all'}
Proof.
  intros n m. intros H.
  rewrite → H.
  reflexivity.
Qed.
```

<div v-click text-2xl pt-3 pl-5>
变量代换？
</div>

---

# 分类讨论！

The `destruct` tactic

又一个“显然”的命题：

```coq
Theorem plus_1_neq_0 : ∀ n : nat,
  (n + 1) =? 0 = false.
```

$\text{eqb}$ 的定义：

```coq
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ eqb n' m'
            end
  end.
```

---

# 分类讨论！

The `destruct` tactic

直接通过 `simpl.` 化简？并不能 😭

<v-click>

原因：$\text{add}$ 与 $\text{eqb}$ 都通过 $\text{match}$ 语句定义。而由于 `n` 是 `O` 还是 `S n'` 是未知的，所以无法直接化简。

</v-click>
<v-click>

使用 `destruct` 策略：

```coq {3|all}
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity. (* E: n = O    *)
  - reflexivity. (* E: n = S n' *)
Qed.
```

</v-click>

---

# 递归地证明

The `induction` tactic：递归地定义 $\Rightarrow$ 递归地证明



<div v-click text-2xl pt-3 pl-5>
分类讨论的升级版？
</div>


```coq editor
Theorem plus_1_neq_0 : ∀ n : nat,
  (n + 1) =? 0 = false.

Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity. (* E: n = O    *)
  - reflexivity. (* E: n = S n' *)
Qed.
```


