include "wcel.mm"
include "cufil.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "cfil.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cfbas.mm"
include "ufilfil.mm"
include "filfbas.mm"
include "syl.mm"
include "fmfil.mm"
include "syl3an2.mm"
include "wa.mm"
include "simpl2.mm"
include "3syl.mm"
include "simprl.mm"
include "simpl3.mm"
include "simprr.mm"
include "fmfnfm.mm"
include "adantr.mm"
include "simprrl.mm"
include "ufilmax.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "simprrr.mm"
include "eqtr4d.mm"
include "rexlimddv.mm"
include "expr.mm"
include "ralrimiva.mm"
include "isufil2.mm"
include "sylanbrc.mm"

theorem fmufil
  let cA: class A
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g


  assert |- ( ( X e. A /\ L e. ( UFil ` Y ) /\ F : Y --> X ) -> ( ( X FilMap F ) ` L ) e. ( UFil ` X ) )

  proof
    cX
    cA
    wcel
    #
    cL
    cY
    cufil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cL
    cX
    cF
    cfm
    co
    #
    cfv
    #
    cX
    cfil
    cfv
    #
    wcel
    #
    @5
    vf
    cv
    #
    wss
    #
    @5
    @8
    wceq
    #
    wi
    #
    vf
    @6
    wral
    @5
    cX
    cufil
    cfv
    wcel
    @1
    @0
    cL
    cY
    cfbas
    cfv
    wcel
    #
    @2
    @7
    @1
    cL
    cY
    cfil
    cfv
    #
    wcel
    #
    @12
    cL
    cY
    ufilfil
    #
    cL
    cY
    filfbas
    #
    syl
    cA
    cL
    cF
    cX
    cY
    fmfil
    syl3an2
    @3
    @11
    vf
    @6
    @3
    @8
    @6
    wcel
    #
    @9
    @10
    @3
    @17
    @9
    wa
    #
    wa
    #
    cL
    vg
    cv
    #
    wss
    #
    @8
    @20
    @4
    cfv
    #
    wceq
    #
    wa
    #
    @10
    vg
    @13
    @19
    cL
    vg
    cF
    @8
    cX
    cY
    @19
    @1
    @14
    @12
    @0
    @1
    @2
    @18
    simpl2
    #
    @15
    @16
    3syl
    @3
    @17
    @9
    simprl
    @0
    @1
    @2
    @18
    simpl3
    @3
    @17
    @9
    simprr
    fmfnfm
    @19
    @20
    @13
    wcel
    #
    @24
    wa
    #
    wa
    #
    @5
    @22
    @8
    @28
    cL
    @20
    @4
    @28
    @1
    @26
    @21
    cL
    @20
    wceq
    @19
    @1
    @27
    @25
    adantr
    @19
    @26
    @24
    simprl
    @19
    @26
    @21
    @23
    simprrl
    cL
    @20
    cY
    ufilmax
    syl3anc
    fveq2d
    @19
    @26
    @21
    @23
    simprrr
    eqtr4d
    rexlimddv
    expr
    ralrimiva
    vf
    @5
    cX
    isufil2
    sylanbrc
end
