include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cima.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wex.mm"
include "simp3.mm"
include "dfss3.mm"
include "fvelrnb.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "biimpa.mm"
include "3adant3.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "fimass.mm"
include "vex.mm"
include "imaex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ad2antrl.mm"
include "wfun.mm"
include "ffun.mm"
include "simpl3.mm"
include "imafi.mm"
include "elind.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wi.mm"
include "fvco3.mm"
include "fvresi.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "ralbidva.mm"
include "biimprd.mm"
include "impr.mm"
include "wb.mm"
include "simpl1.mm"
include "ffn.mm"
include "frn.mm"
include "fnco.mm"
include "syl3anc.mm"
include "fnresi.mm"
include "eqfnfv.mm"
include "sylancl.mm"
include "mpbird.mm"
include "imaeq1d.mm"
include "imaco.mm"
include "ssid.mm"
include "resiima.mm"
include "ax-mp.mm"
include "3eqtr3g.mm"
include "imaeq2.mm"
include "rspcev.mm"
include "exlimddv.mm"

theorem fipreima
  let cA: class A
  let cB: class B
  let cF: class F
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y

  disjoint A c
  disjoint B c
  disjoint F c
  disjoint A f
  disjoint c f
  disjoint A x
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f x
  disjoint f y
  assert |- ( ( F Fn B /\ A C_ ran F /\ A e. Fin ) -> E. c e. ( ~P B i^i Fin ) ( F " c ) = A )

  proof
    cF
    cB
    wfn
    #
    cA
    cF
    crn
    #
    wss
    #
    cA
    cfn
    wcel
    #
    w3a
    #
    cA
    cB
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    @5
    cfv
    #
    cF
    cfv
    #
    @7
    wceq
    #
    vx
    cA
    wral
    #
    wa
    #
    cF
    vc
    cv
    #
    cima
    #
    cA
    wceq
    #
    vc
    cB
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vf
    @4
    @3
    vy
    cv
    #
    cF
    cfv
    #
    @7
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @12
    vf
    wex
    @0
    @2
    @3
    simp3
    @0
    @2
    @23
    @3
    @0
    @2
    @23
    @2
    @7
    @1
    wcel
    #
    vx
    cA
    wral
    @0
    @23
    vx
    cA
    @1
    dfss3
    @0
    @24
    @22
    vx
    cA
    vy
    cB
    @7
    cF
    fvelrnb
    ralbidv
    syl5bb
    biimpa
    3adant3
    @21
    @10
    vx
    vy
    cA
    cB
    vf
    @19
    @8
    wceq
    @20
    @9
    @7
    @19
    @8
    cF
    fveq2
    eqeq1d
    ac6sfi
    syl2anc
    @4
    @12
    wa
    #
    @5
    cA
    cima
    #
    @17
    wcel
    cF
    @26
    cima
    #
    cA
    wceq
    #
    @18
    @25
    @16
    cfn
    @26
    @6
    @26
    @16
    wcel
    #
    @4
    @11
    @6
    @26
    cB
    wss
    @29
    cA
    cB
    @5
    cA
    fimass
    @26
    cB
    @5
    cA
    vf
    vex
    imaex
    elpw
    sylibr
    ad2antrl
    @25
    @5
    wfun
    #
    @3
    @26
    cfn
    wcel
    @6
    @30
    @4
    @11
    cA
    cB
    @5
    ffun
    ad2antrl
    @0
    @2
    @3
    @12
    simpl3
    @5
    cA
    imafi
    syl2anc
    elind
    @25
    cF
    @5
    ccom
    #
    cA
    cima
    cid
    cA
    cres
    #
    cA
    cima
    #
    @27
    cA
    @25
    @31
    @32
    cA
    @25
    @31
    @32
    wceq
    #
    @7
    @31
    cfv
    #
    @7
    @32
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @4
    @6
    @11
    @38
    @6
    @11
    @38
    wi
    @4
    @6
    @38
    @11
    @6
    @37
    @10
    vx
    cA
    @6
    @7
    cA
    wcel
    #
    wa
    @35
    @9
    @36
    @7
    cA
    cB
    @7
    cF
    @5
    fvco3
    @39
    @36
    @7
    wceq
    @6
    cA
    @7
    fvresi
    adantl
    eqeq12d
    ralbidva
    biimprd
    adantl
    impr
    @25
    @31
    cA
    wfn
    #
    @32
    cA
    wfn
    @34
    @38
    wb
    @25
    @0
    @5
    cA
    wfn
    #
    @5
    crn
    cB
    wss
    #
    @40
    @0
    @2
    @3
    @12
    simpl1
    @6
    @41
    @4
    @11
    cA
    cB
    @5
    ffn
    ad2antrl
    @6
    @42
    @4
    @11
    cA
    cB
    @5
    frn
    ad2antrl
    cB
    cA
    cF
    @5
    fnco
    syl3anc
    cA
    fnresi
    vx
    cA
    @31
    @32
    eqfnfv
    sylancl
    mpbird
    imaeq1d
    cF
    @5
    cA
    imaco
    cA
    cA
    wss
    @33
    cA
    wceq
    cA
    ssid
    cA
    cA
    resiima
    ax-mp
    3eqtr3g
    @15
    @28
    vc
    @26
    @17
    @13
    @26
    wceq
    @14
    @27
    cA
    @13
    @26
    cF
    imaeq2
    eqeq1d
    rspcev
    syl2anc
    exlimddv
end
