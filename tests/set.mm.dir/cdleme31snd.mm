include "wcel.mm"
include "csb.mm"
include "csbnestg.mm"
include "cdleme31sc.mm"
include "csbeq1d.mm"
include "cvv.mm"
include "wceq.mm"
include "co.mm"
include "ovexi.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem cdleme31snd
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cE: class E
  let c.or: class .\/
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  assume cdleme31snd.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme31snd.n: |- N = ( ( v .\/ V ) ./\ ( P .\/ ( ( Q .\/ v ) ./\ W ) ) )
  assume cdleme31snd.e: |- E = ( ( O .\/ U ) ./\ ( Q .\/ ( ( P .\/ O ) ./\ W ) ) )
  assume cdleme31snd.o: |- O = ( ( S .\/ V ) ./\ ( P .\/ ( ( Q .\/ S ) ./\ W ) ) )

  disjoint A v
  disjoint D v
  disjoint t v
  disjoint .\/ t
  disjoint .\/ v
  disjoint ./\ t
  disjoint ./\ v
  disjoint O t
  disjoint P t
  disjoint P v
  disjoint Q t
  disjoint Q v
  disjoint S v
  disjoint U t
  disjoint U v
  disjoint V v
  disjoint W t
  disjoint W v
  assert |- ( S e. A -> [_ S / v ]_ [_ N / t ]_ D = E )

  proof
    cS
    cA
    wcel
    #
    vv
    cS
    vt
    cN
    cD
    csb
    csb
    vt
    vv
    cS
    cN
    csb
    #
    cD
    csb
    #
    cE
    vv
    vt
    cS
    cN
    cD
    cA
    csbnestg
    @0
    @2
    vt
    cO
    cD
    csb
    #
    cE
    @0
    vt
    @1
    cO
    cD
    cA
    cN
    cQ
    cP
    cS
    cV
    c.or
    c.an
    cW
    cO
    vv
    cdleme31snd.n
    cdleme31snd.o
    cdleme31sc
    csbeq1d
    cO
    cvv
    wcel
    @3
    cE
    wceq
    cO
    cS
    cV
    c.or
    co
    cP
    cQ
    cS
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    cdleme31snd.o
    ovexi
    cvv
    cD
    cP
    cQ
    cO
    cU
    c.or
    c.an
    cW
    cE
    vt
    cdleme31snd.d
    cdleme31snd.e
    cdleme31sc
    ax-mp
    syl6eq
    eqtrd
end
