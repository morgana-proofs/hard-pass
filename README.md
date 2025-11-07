# Investigation of hard sumcheck in Twist & Shout memory argument

This version of Twist works as follows:

There is a $\mathsf{diff}(t)$ polynomial and $\mathsf{acc}(t)$ polynomial
There is also $\mathsf{init}(x)$ polynomial, which normally = 0, but sometimes it could be not (say if we are doing continuation).

Read in this version happens after diff, so actually it is write, and actual read is obtained by subtracting diff. We do $|t|$ diffs and $|t|$ reads and values of ram do not include $\mathsf{init}(x)$ but do include the last state.

### Stages of the protocol

The protocol includes the following stages (listed here in dataflow order, so last one will be ran first).

1. $\mathsf{acc}(t)$ is upgraded to $\mathsf{Acc}(x, t)$ (presumably using logup*). This is the difference with normal Twist, which straight up commits to $\mathsf{Acc}$
    To evaluate $\mathsf{Acc}(r_x, r_t)$ we need to compute $\langle \mathsf{acc}_* \mathsf{eq}_{r_t}, \mathsf{eq}_{r_x}\rangle$. The validity of $\mathsf{acc}_* \mathsf{eq}_{r_t}$ is checked by logup* argument. Square-decomposition is not done because we assume RAM to be relatively small ($|x| << |t|$).

2. A polynomial $\mathsf{RAM}(x, t) = \mathsf{init}(x) + \underset{t'}\sum \mathsf{Lt}(t', t) \mathsf{Acc}(x, t') \mathsf{diff}(t')$. 
    This sumcheck is only over $t'$, so it is relatively cheap.

3. A polynomial $\mathsf{read}(t) = \underset{x, t'}\sum \mathsf{RAM}(x, t') \mathsf{Acc}(x, t') \mathsf{eq}(t, t')$.
    This phase is hard because the sumcheck here is sparse.

We will refer to them as "read phase", "sum phase" and "spark phase". Read phase is hard. Note: we might rename read phase to write phase at some point, considering read is actually write...

### Read phase

The main purpose of this project is to investigate whether this sparse sumcheck is worth it compared to more standard permutation-based arguments, and, separately, to provide reference implementation of Twist without sparse commitment scheme.

Twist has other advantages (for example, it can natively support vectorized loads and stores only with a very minor modification).

Starting from the evaluation claim for $\mathsf{read}(r_t)$Current method for passing the hard phase works as follows:

1. We define a RAM structure, which contains diffs, access addresses and "twists". Initial twists are set to be values of polynomial $\mathsf{eq}_{r_t}$. In general, during the sumcheck, the twist will be a product of values of $\mathsf{Acc}(x, t)$ and $\mathsf{eq}_{r_t}(t)$. So when we bind some of $x$-variables, $\mathsf{Acc}$ stops being 1-hot - but we redistribute these values to multipliers. This does not affect $x$-rounds (while it would definitely break multilinear extension along $t$). In the end of $x$-rounds we recover actual values of restriction of $\mathsf{Acc}$ by dividing back by $\mathsf{eq}_{r_t}$.
2. The individual $x$-round's response is calculated as follows: we make a single scan through RAM, and for each access $a$ at time $t$ take the values `state[a / 2 * 2], state[a / 2 * 2 + 1]`, multiply them by corrseponding multiplier and add them to the one of two buckets depending on the value of `a%2`. One of those buckets will then interact with linear polynomial acc `[1, 0]` and other with `[0, 1]`.
3. To compute new RAM state we multiply twists by `if(a % 2 == 0) {ONE - u} else{u}`, divide value of all accesses by $2$ and also bind initial state.
4. In real instantiation, we also make few snapshots of RAM to parallelize. Each of those works as "initial state" for the temporal chunk being processed.
5. After $x$-rounds finish, we recover actual values of $\mathsf{Acc}(u_x, t)$ by dividing twists by values of $eq_{r_t}$, and just run a dense sumcheck protocol along $t$.

Note: in Twist & Shout paper, another approach is proposed, interspersing $x$ and $t$ rounds, which should be better for localized accesses. We currently did not check whether it makes any sense (and access pattern we currently run my benchmarks with is random). Also, bucketing strategy will not work in this case as far as I understand, so it will be an actual sparse sumcheck.