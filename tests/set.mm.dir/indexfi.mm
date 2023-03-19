include "cfn.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "wf.mm"
include "cfv.mm"
include "wsbc.mm"
include "wex.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "sbceq1a.mm"
include "cbvrex.mm"
include "ralbii.mm"
include "dfsbcq.mm"
include "ac6sfi.mm"
include "sylan2b.mm"
include "crn.mm"
include "wfo.mm"
include "simpll.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antrl.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "syl2anc.mm"
include "frn.mm"
include "wi.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "rspesbca.mm"
include "ex.mm"
include "syl.mm"
include "ralimdva.mm"
include "imp.mm"
include "adantl.mm"
include "simpr.mm"
include "simprr.mm"
include "weq.mm"
include "fveq2.mm"
include "sbceq1d.mm"
include "bitrd.mm"
include "cbvral.mm"
include "r19.21bi.mm"
include "ralrimiva.mm"
include "wb.mm"
include "wceq.mm"
include "rexbidv.mm"
include "ralrn.mm"
include "mpbird.mm"
include "nfcv.mm"
include "nfrex.mm"
include "sylibr.mm"
include "sseq1.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "raleq.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "exlimddv.mm"
include "3adant2.mm"

theorem indexfi
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cM: class M
  let vc: setvar c
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z

  disjoint c x
  disjoint c y
  disjoint A c
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B c
  disjoint B x
  disjoint B y
  disjoint c ph
  disjoint c f
  disjoint c w
  disjoint c z
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B w
  disjoint B z
  disjoint f ph
  disjoint ph w
  disjoint ph z
  assert |- ( ( A e. Fin /\ B e. M /\ A. x e. A E. y e. B ph ) -> E. c e. Fin ( c C_ B /\ A. x e. A E. y e. c ph /\ A. y e. c E. x e. A ph ) )

  proof
    cA
    cfn
    wcel
    #
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    vc
    cv
    #
    cB
    wss
    #
    wph
    vy
    @3
    wrex
    #
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wrex
    #
    vy
    @3
    wral
    #
    w3a
    #
    vc
    cfn
    wrex
    #
    cB
    cM
    wcel
    @0
    @2
    wa
    #
    cA
    cB
    vf
    cv
    #
    wf
    #
    wph
    vy
    vx
    cv
    #
    @12
    cfv
    #
    wsbc
    #
    vx
    cA
    wral
    #
    wa
    #
    @10
    vf
    @2
    @0
    wph
    vy
    vz
    cv
    #
    wsbc
    #
    vz
    cB
    wrex
    #
    vx
    cA
    wral
    @18
    vf
    wex
    @1
    @21
    vx
    cA
    wph
    @20
    vy
    vz
    cB
    wph
    vz
    nfv
    wph
    vy
    @19
    nfsbc1v
    #
    wph
    vy
    @19
    sbceq1a
    #
    cbvrex
    ralbii
    @20
    @16
    vx
    vz
    cA
    cB
    vf
    wph
    vy
    @19
    @15
    dfsbcq
    ac6sfi
    sylan2b
    @11
    @18
    wa
    #
    @12
    crn
    #
    cfn
    wcel
    #
    @25
    cB
    wss
    #
    wph
    vy
    @25
    wrex
    #
    vx
    cA
    wral
    #
    @7
    vy
    @25
    wral
    #
    @10
    @24
    @0
    cA
    @25
    @12
    wfo
    #
    @26
    @0
    @2
    @18
    simpll
    @24
    @12
    cA
    wfn
    #
    @31
    @13
    @32
    @11
    @17
    cA
    cB
    @12
    ffn
    #
    ad2antrl
    #
    cA
    @12
    dffn4
    sylib
    cA
    @25
    @12
    fofi
    syl2anc
    @13
    @27
    @11
    @17
    cA
    cB
    @12
    frn
    ad2antrl
    @18
    @29
    @11
    @13
    @17
    @29
    @13
    @16
    @28
    vx
    cA
    @13
    @14
    cA
    wcel
    #
    wa
    @15
    @25
    wcel
    #
    @16
    @28
    wi
    @13
    @32
    @35
    @36
    @33
    cA
    @14
    @12
    fnfvelrn
    sylan
    @36
    @16
    @28
    wph
    vy
    @15
    @25
    rspesbca
    ex
    syl
    ralimdva
    imp
    adantl
    @24
    @20
    vx
    cA
    wrex
    #
    vz
    @25
    wral
    #
    @30
    @24
    @38
    wph
    vy
    vw
    cv
    #
    @12
    cfv
    #
    wsbc
    #
    vx
    cA
    wrex
    #
    vw
    cA
    wral
    #
    @24
    @42
    vw
    cA
    @24
    @39
    cA
    wcel
    #
    wa
    @44
    @41
    vx
    @39
    wsbc
    #
    @42
    @24
    @44
    simpr
    @24
    @45
    vw
    cA
    @24
    @17
    @45
    vw
    cA
    wral
    @11
    @13
    @17
    simprr
    @16
    @45
    vx
    vw
    cA
    @16
    vw
    nfv
    @41
    vx
    @39
    nfsbc1v
    vx
    vw
    weq
    #
    @16
    @41
    @45
    @46
    wph
    vy
    @15
    @40
    @14
    @39
    @12
    fveq2
    sbceq1d
    @41
    vx
    @39
    sbceq1a
    bitrd
    cbvral
    sylib
    r19.21bi
    @41
    vx
    @39
    cA
    rspesbca
    syl2anc
    ralrimiva
    @24
    @32
    @38
    @43
    wb
    @34
    @37
    @42
    vz
    vw
    cA
    @12
    @19
    @40
    wceq
    @20
    @41
    vx
    cA
    wph
    vy
    @19
    @40
    dfsbcq
    rexbidv
    ralrn
    syl
    mpbird
    @7
    @37
    vy
    vz
    @25
    @7
    vz
    nfv
    @20
    vy
    vx
    cA
    vy
    cA
    nfcv
    @22
    nfrex
    vy
    vz
    weq
    wph
    @20
    vx
    cA
    @23
    rexbidv
    cbvral
    sylibr
    @9
    @27
    @29
    @30
    w3a
    vc
    @25
    cfn
    @3
    @25
    wceq
    #
    @4
    @27
    @6
    @29
    @8
    @30
    @3
    @25
    cB
    sseq1
    @47
    @5
    @28
    vx
    cA
    wph
    vy
    @3
    @25
    rexeq
    ralbidv
    @7
    vy
    @3
    @25
    raleq
    3anbi123d
    rspcev
    syl13anc
    exlimddv
    3adant2
end
