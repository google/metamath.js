include "cusgr.mm"
include "wcel.mm"
include "cushgr.mm"
include "wf1o.mm"
include "cuspgr.mm"
include "usgruspgr.mm"
include "uspgrushgr.mm"
include "syl.mm"
include "ushgredgedg.mm"
include "sylan.mm"

theorem usgredgedg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let ve: setvar e
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vj: setvar j
  assume ushgredgedg.e: |- E = ( Edg ` G )
  assume ushgredgedg.i: |- I = ( iEdg ` G )
  assume ushgredgedg.v: |- V = ( Vtx ` G )
  assume ushgredgedg.a: |- A = { i e. dom I | N e. ( I ` i ) }
  assume ushgredgedg.b: |- B = { e e. E | N e. e }
  assume ushgredgedg.f: |- F = ( x e. A |-> ( I ` x ) )

  disjoint B e
  disjoint E e
  disjoint E i
  disjoint e i
  disjoint G e
  disjoint G i
  disjoint G x
  disjoint I e
  disjoint I i
  disjoint I x
  disjoint e x
  disjoint i x
  disjoint N e
  disjoint N i
  disjoint N x
  disjoint V e
  disjoint V i
  disjoint V x
  disjoint B f
  disjoint e f
  disjoint E j
  disjoint e j
  disjoint i j
  disjoint G f
  disjoint G j
  disjoint f i
  disjoint f j
  disjoint I f
  disjoint I j
  disjoint N f
  disjoint N j
  disjoint V f
  disjoint V j
  assert |- ( ( G e. USGraph /\ N e. V ) -> F : A -1-1-onto-> B )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cushgr
    wcel
    #
    cN
    cV
    wcel
    cA
    cB
    cF
    wf1o
    @0
    cG
    cuspgr
    wcel
    @1
    cG
    usgruspgr
    cG
    uspgrushgr
    syl
    vx
    cA
    cB
    ve
    vi
    cE
    cF
    cG
    cI
    cN
    cV
    ushgredgedg.e
    ushgredgedg.i
    ushgredgedg.v
    ushgredgedg.a
    ushgredgedg.b
    ushgredgedg.f
    ushgredgedg
    sylan
end
