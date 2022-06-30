<p align="center"> <img src="/static/toadml.png" alt="logo" width="400" style="display:block;margin-left: auto;margin-right: auto;"></p>
<h1 align="center">ToadML</h1>

<p align="center">
    <img src="https://img.shields.io/maintenance/yes/2022?style=flat-square" alt="logo">
</p>
<br>

This is a research-grade, hobby programminglanguage.

## Introduction

The goal of ToadML is to make a truly safe language. That is, any kind of safety:

- memory safety
- safely using some legacy API
- safely doing FFI calls
- ...

True safety is achieved by formal methods (and in some cases, you just have to do dynamic checks), henceforth the language design makes use of dependent types to prove stuff about your algorithms from within the language itself. Unfortunately, the fire triangle, as depicted in Figure 1, shows that we cannot have a practical programming language that has a *consistent* dependent type system.

<p align="center"><img src="/static/firetriangle.png" alt="firetriangle" height="300" style="display:block;margin-left:auto;margin-right:auto;"></p>
<p align="center"><b>Figure 1:</b> Fire triangle as depicted in "<a href="https://www.xn--pdrot-bsa.fr/articles/dcbpv.pdf">The Fire Triangle</a>, by PÉDROT and TABAREAU.</p>

Our solution to this issue is to employ a multi-level programming language. The idea is to have a language that is completely runtime irrelevant and another one where terms may be meaningful in terms of runtime. Both have "their own typesystem", however, there is a way to translate from one sysetm to the other. To reduce confusion and because I simply do not have a name for these two languages, I'll refer to the runtime irrelevant one as "higher" and the runtime-relevant one as "lower"-level language. The intuition is that there are multiple stages where the respective languages reside in. In turn, we can write specifications in the higher language for the lower and verify algorithms that have been written in the lower language.

The lower language is also more low level in the sense that its types are closer to the machine representations. For example, while there may be some kind of "unique pointer type", the higher language simply doesn't have this, since there are no values at that level which inhabit it.

By leaveraging an algebraic effect system to e.g. perform the usual syscalls/the "interesting" stuff in terms of "things may go wrong", we should be able to abstractly reason about runtime-program traces and verify individual trace-properties of interest in the higher language. Users should be able to declare the algebraic operations that come along with the effects and, upon defining appropriate handlers, verify that they hold for the respective handlers. Unfortunately, algebraic effects have a major "wart": The same piece of code may run differently depending on the *order* of how handlers are applied. Up to my knowledge, there is no real solution right now, so we'll make up our own as we go. My guess is that it should be fine to simply somehow make the order fixed.

I've mentioned that in the lower language, terms *may* be runtime-relevant. The reason why not all such terms are runtime-relevant is simple: we will make heavy use of a partial evaluator on the level of that language. Henceforth, some terms may simply be optimized away aggressively. 

Finally, even though the language is supposed to be "truly" secure, without certain hardware (e.g. Intel SGX) being more commonly used, there is basically no chance to achieve that goal *truly*. On the bright side, you don't want to be secure for *everything*, *always*. Why? Think about cryptographic libraries. Here, you are interested in the hyperproperty cryptographic constant-time. That is, any program execution takes exactly the same amount of time regardless of the public input. If this is not the case, an adversary may read off your secrets by a simple timing analysis! So, you do want this property in parts there, but you certainly don't want this property in high-performance environments where you are crunching numbers and where it really makes a difference to optimize away the `x * 0` and just do the `0`. Or, maybe, you are just not in such a super secure setting and may only need the usual string-compare functionality that is not cryptographic constant-time.

The project is licensed under the Apache License.