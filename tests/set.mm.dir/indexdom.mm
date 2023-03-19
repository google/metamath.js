include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wsbc.mm"
include "wex.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "nfsbc1v.mm"
include "sbceq1a.mm"
include "ac6gf.mm"
include "crn.mm"
include "cvv.mm"
include "wfn.mm"
include "cdm.mm"
include "fdm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "ffn.mm"
include "fnrndomg.mm"
include "sylc.mm"
include "adantr.mm"
include "frn.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "wfun.mm"
include "ffun.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "rspa.mm"
include "adantll.mm"
include "rspesbca.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfcv.mm"
include "nfral.mm"
include "wceq.mm"
include "wb.mm"
include "fvelrnb.mm"
include "syl.mm"
include "wi.mm"
include "rsp.mm"
include "adantl.mm"
include "eqcoms.mm"
include "biimprcd.mm"
include "syl6.mm"
include "reximdai.mm"
include "sylbid.mm"
include "rnex.mm"
include "breq1.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "raleq.mm"
include "spcev.mm"
include "syl22anc.mm"
include "exlimiv.mm"

theorem indexdom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cM: class M
  let vc: setvar c
  let vf: setvar f

  disjoint A c
  disjoint A x
  disjoint A y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint B c
  disjoint B x
  disjoint B y
  disjoint c ph
  disjoint A f
  disjoint c f
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint f ph
  assert |- ( ( A e. M /\ A. x e. A E. y e. B ph ) -> E. c ( ( c ~<_ A /\ c C_ B ) /\ ( A. x e. A E. y e. c ph /\ A. y e. c E. x e. A ph ) ) )

  proof
    cA
    cM
    wcel
    wph
    vy
    cB
    wrex
    vx
    cA
    wral
    wa
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
    @0
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
    vf
    wex
    vc
    cv
    #
    cA
    cdom
    wbr
    #
    @7
    cB
    wss
    #
    wa
    #
    wph
    vy
    @7
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
    @7
    wral
    #
    wa
    #
    wa
    #
    vc
    wex
    #
    wph
    @4
    vx
    vy
    cA
    cB
    cM
    vf
    wph
    vy
    @3
    nfsbc1v
    #
    wph
    vy
    @3
    sbceq1a
    #
    ac6gf
    @6
    @17
    vf
    @6
    @0
    crn
    #
    cA
    cdom
    wbr
    #
    @20
    cB
    wss
    #
    wph
    vy
    @20
    wrex
    #
    vx
    cA
    wral
    #
    @13
    vy
    @20
    wral
    #
    @17
    @1
    @21
    @5
    @1
    cA
    cvv
    wcel
    @0
    cA
    wfn
    #
    @21
    @1
    cA
    @0
    cdm
    #
    cvv
    cA
    cB
    @0
    fdm
    #
    @0
    vf
    vex
    #
    dmex
    syl6eqelr
    cA
    cB
    @0
    ffn
    #
    cA
    cvv
    @0
    fnrndomg
    sylc
    adantr
    @1
    @22
    @5
    cA
    cB
    @0
    frn
    adantr
    @6
    @23
    vx
    cA
    @1
    @5
    vx
    @1
    vx
    nfv
    @4
    vx
    cA
    nfra1
    nfan
    #
    @6
    @2
    cA
    wcel
    #
    @23
    @6
    @32
    wa
    @3
    @20
    wcel
    #
    @4
    @23
    @1
    @32
    @33
    @5
    @1
    @32
    wa
    @0
    wfun
    #
    @2
    @27
    wcel
    #
    @33
    @1
    @34
    @32
    cA
    cB
    @0
    ffun
    adantr
    @1
    @35
    @32
    @1
    @27
    cA
    @2
    @28
    eleq2d
    biimpar
    @2
    @0
    fvelrn
    syl2anc
    adantlr
    @5
    @32
    @4
    @1
    @4
    vx
    cA
    rspa
    adantll
    wph
    vy
    @3
    @20
    rspesbca
    syl2anc
    ex
    ralrimi
    @6
    @13
    vy
    @20
    @1
    @5
    vy
    @1
    vy
    nfv
    @4
    vy
    vx
    cA
    vy
    cA
    nfcv
    @18
    nfral
    nfan
    @6
    vy
    cv
    #
    @20
    wcel
    #
    @3
    @36
    wceq
    #
    vx
    cA
    wrex
    #
    @13
    @1
    @37
    @39
    wb
    #
    @5
    @1
    @26
    @40
    @30
    vx
    cA
    @36
    @0
    fvelrnb
    syl
    adantr
    @6
    @38
    wph
    vx
    cA
    @31
    @6
    @32
    @4
    @38
    wph
    wi
    @5
    @32
    @4
    wi
    @1
    @4
    vx
    cA
    rsp
    adantl
    @38
    wph
    @4
    wph
    @4
    wb
    @36
    @3
    @19
    eqcoms
    biimprcd
    syl6
    reximdai
    sylbid
    ralrimi
    @16
    @21
    @22
    wa
    #
    @24
    @25
    wa
    #
    wa
    vc
    @20
    @0
    @29
    rnex
    @7
    @20
    wceq
    #
    @10
    @41
    @15
    @42
    @43
    @8
    @21
    @9
    @22
    @7
    @20
    cA
    cdom
    breq1
    @7
    @20
    cB
    sseq1
    anbi12d
    @43
    @12
    @24
    @14
    @25
    @43
    @11
    @23
    vx
    cA
    wph
    vy
    @7
    @20
    rexeq
    ralbidv
    @13
    vy
    @7
    @20
    raleq
    anbi12d
    anbi12d
    spcev
    syl22anc
    exlimiv
    syl
end
