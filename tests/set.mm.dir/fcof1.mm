include "wf.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "simpl.mm"
include "wcel.mm"
include "simprr.mm"
include "fveq2d.mm"
include "simpll.mm"
include "simprll.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "simprlr.mm"
include "3eqtr4d.mm"
include "simplr.mm"
include "fveq1d.mm"
include "3eqtr3d.mm"
include "fvresi.mm"
include "syl.mm"
include "expr.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem fcof1
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A --> B /\ ( R o. F ) = ( _I |` A ) ) -> F : A -1-1-> B )

  proof
    cA
    cB
    cF
    wf
    #
    cR
    cF
    ccom
    #
    cid
    cA
    cres
    #
    wceq
    #
    wa
    #
    @0
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @5
    @7
    wceq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    cA
    cB
    cF
    wf1
    @0
    @3
    simpl
    @4
    @11
    vx
    vy
    cA
    cA
    @4
    @5
    cA
    wcel
    #
    @7
    cA
    wcel
    #
    wa
    #
    @9
    @10
    @4
    @14
    @9
    wa
    #
    wa
    #
    @5
    @2
    cfv
    #
    @7
    @2
    cfv
    #
    @5
    @7
    @16
    @5
    @1
    cfv
    #
    @7
    @1
    cfv
    #
    @17
    @18
    @16
    @6
    cR
    cfv
    #
    @8
    cR
    cfv
    #
    @19
    @20
    @16
    @6
    @8
    cR
    @4
    @14
    @9
    simprr
    fveq2d
    @16
    @0
    @12
    @19
    @21
    wceq
    @0
    @3
    @15
    simpll
    #
    @4
    @12
    @13
    @9
    simprll
    #
    cA
    cB
    @5
    cR
    cF
    fvco3
    syl2anc
    @16
    @0
    @13
    @20
    @22
    wceq
    @23
    @4
    @12
    @13
    @9
    simprlr
    #
    cA
    cB
    @7
    cR
    cF
    fvco3
    syl2anc
    3eqtr4d
    @16
    @5
    @1
    @2
    @0
    @3
    @15
    simplr
    #
    fveq1d
    @16
    @7
    @1
    @2
    @26
    fveq1d
    3eqtr3d
    @16
    @12
    @17
    @5
    wceq
    @24
    cA
    @5
    fvresi
    syl
    @16
    @13
    @18
    @7
    wceq
    @25
    cA
    @7
    fvresi
    syl
    3eqtr3d
    expr
    ralrimivva
    vx
    vy
    cA
    cB
    cF
    dff13
    sylanbrc
end
