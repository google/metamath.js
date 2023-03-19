include "crs.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "crh.mm"
include "wf1.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "rimrhm.mm"
include "wf1o.mm"
include "rimf1o.mm"
include "f1of1.mm"
include "syl.mm"
include "jca.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "f1rhm0to0.mm"

theorem rim0to0
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume f1rhm0to0.a: |- A = ( Base ` R )
  assume f1rhm0to0.b: |- B = ( Base ` S )
  assume f1rhm0to0.n: |- N = ( 0g ` S )
  assume f1rhm0to0.0: |- .0. = ( 0g ` R )


  assert |- ( ( F e. ( R RingIso S ) /\ X e. A ) -> ( ( F ` X ) = N <-> X = .0. ) )

  proof
    cF
    cR
    cS
    crs
    co
    wcel
    #
    cX
    cA
    wcel
    #
    wa
    #
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    @1
    w3a
    #
    cX
    cF
    cfv
    cN
    wceq
    cX
    c.0
    wceq
    wb
    @2
    @3
    @4
    wa
    #
    @1
    wa
    @5
    @0
    @6
    @1
    @0
    @3
    @4
    cA
    cB
    cR
    cS
    cF
    f1rhm0to0.a
    f1rhm0to0.b
    rimrhm
    @0
    cA
    cB
    cF
    wf1o
    @4
    cA
    cB
    cR
    cS
    cF
    f1rhm0to0.a
    f1rhm0to0.b
    rimf1o
    cA
    cB
    cF
    f1of1
    syl
    jca
    anim1i
    @3
    @4
    @1
    df-3an
    sylibr
    cA
    cB
    cR
    cS
    cF
    cN
    cX
    c.0
    f1rhm0to0.a
    f1rhm0to0.b
    f1rhm0to0.n
    f1rhm0to0.0
    f1rhm0to0
    syl
end
