include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "elmapg.mm"
include "ancoms.mm"
include "biimp3ar.mm"
include "fvmpt.mm"
include "syl.mm"

theorem fvopabf4g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  assume fvopabf4g.1: |- C e. _V
  assume fvopabf4g.2: |- ( x = A -> B = C )
  assume fvopabf4g.3: |- F = ( x e. ( R ^m D ) |-> B )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint R x
  assert |- ( ( D e. X /\ R e. Y /\ A : D --> R ) -> ( F ` A ) = C )

  proof
    cD
    cX
    wcel
    #
    cR
    cY
    wcel
    #
    cD
    cR
    cA
    wf
    #
    w3a
    cA
    cR
    cD
    cmap
    co
    #
    wcel
    #
    cA
    cF
    cfv
    cC
    wceq
    @0
    @1
    @4
    @2
    @1
    @0
    @4
    @2
    wb
    cR
    cD
    cA
    cY
    cX
    elmapg
    ancoms
    biimp3ar
    vx
    cA
    cB
    cC
    @3
    cF
    fvopabf4g.2
    fvopabf4g.3
    fvopabf4g.1
    fvmpt
    syl
end
