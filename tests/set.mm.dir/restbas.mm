include "ctb.mm"
include "wcel.mm"
include "cvv.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wceq.mm"
include "elrest.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "syl6bbr.mm"
include "simplll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "inss1.mm"
include "simpr.mm"
include "sseldi.mm"
include "basis2.mm"
include "syl22anc.mm"
include "simpld.mm"
include "simprd.mm"
include "simprl.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "simprrl.mm"
include "inss2.mm"
include "simplr.mm"
include "elind.mm"
include "simprrr.mm"
include "ssrin.mm"
include "syl.mm"
include "eleq2.mm"
include "sseq1.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "ralrimiva.mm"
include "ineq12.mm"
include "inindir.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "raleqbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "wb.mm"
include "ovex.mm"
include "isbasis2g.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "wrel.mm"
include "cxp.mm"
include "relxp.mm"
include "wfn.mm"
include "restfn.mm"
include "fndm.mm"
include "releqi.mm"
include "mpbir.mm"
include "ovprc2.mm"
include "adantl.mm"
include "cfi.mm"
include "cfv.mm"
include "fi0.mm"
include "fibas.mm"
include "eqeltrri.mm"
include "syl6eqel.mm"
include "pm2.61dan.mm"

theorem restbas
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cX: class X
  let cV: class V
  let cW: class W


  assert |- ( B e. TopBases -> ( B |`t A ) e. TopBases )

  proof
    cB
    ctb
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cA
    crest
    co
    #
    ctb
    wcel
    #
    @0
    @1
    wa
    #
    vc
    cv
    #
    vw
    cv
    #
    wcel
    #
    @6
    va
    cv
    #
    vb
    cv
    #
    cin
    #
    wss
    #
    wa
    #
    vw
    @2
    wrex
    #
    vc
    @10
    wral
    #
    vb
    @2
    wral
    va
    @2
    wral
    #
    @3
    @4
    @14
    va
    vb
    @2
    @2
    @4
    @8
    @2
    wcel
    #
    @9
    @2
    wcel
    #
    wa
    #
    @8
    vu
    cv
    #
    cA
    cin
    #
    wceq
    #
    @9
    vv
    cv
    #
    cA
    cin
    #
    wceq
    #
    wa
    #
    vv
    cB
    wrex
    vu
    cB
    wrex
    #
    @14
    @4
    @18
    @21
    vu
    cB
    wrex
    #
    @24
    vv
    cB
    wrex
    #
    wa
    @26
    @4
    @16
    @27
    @17
    @28
    vu
    @8
    cA
    cB
    ctb
    cvv
    elrest
    vv
    @9
    cA
    cB
    ctb
    cvv
    elrest
    anbi12d
    @21
    @24
    vu
    vv
    cB
    cB
    reeanv
    syl6bbr
    @4
    @25
    @14
    vu
    vv
    cB
    cB
    @4
    @19
    cB
    wcel
    #
    @22
    cB
    wcel
    #
    wa
    #
    wa
    #
    @14
    @25
    @7
    @6
    @19
    @22
    cin
    #
    cA
    cin
    #
    wss
    #
    wa
    #
    vw
    @2
    wrex
    #
    vc
    @34
    wral
    @32
    @37
    vc
    @34
    @32
    @5
    @34
    wcel
    #
    wa
    #
    @5
    vz
    cv
    #
    wcel
    #
    @40
    @33
    wss
    #
    wa
    #
    @37
    vz
    cB
    @39
    @0
    @29
    @30
    @5
    @33
    wcel
    @43
    vz
    cB
    wrex
    @0
    @1
    @31
    @38
    simplll
    @4
    @29
    @30
    @38
    simplrl
    @4
    @29
    @30
    @38
    simplrr
    @39
    @34
    @33
    @5
    @33
    cA
    inss1
    @32
    @38
    simpr
    sseldi
    vz
    @5
    cB
    @19
    @22
    basis2
    syl22anc
    @39
    @40
    cB
    wcel
    #
    @43
    wa
    #
    wa
    #
    @40
    cA
    cin
    #
    @2
    wcel
    #
    @5
    @47
    wcel
    #
    @47
    @34
    wss
    #
    @37
    @46
    @0
    @1
    @44
    @48
    @46
    @0
    @1
    @4
    @31
    @38
    @45
    simplll
    #
    simpld
    @46
    @0
    @1
    @51
    simprd
    @39
    @44
    @43
    simprl
    @40
    cA
    cB
    ctb
    cvv
    elrestr
    syl3anc
    @46
    @40
    cA
    @5
    @39
    @44
    @41
    @42
    simprrl
    @46
    @34
    cA
    @5
    @33
    cA
    inss2
    @32
    @38
    @45
    simplr
    sseldi
    elind
    @46
    @42
    @50
    @39
    @44
    @41
    @42
    simprrr
    @40
    @33
    cA
    ssrin
    syl
    @36
    @49
    @50
    wa
    vw
    @47
    @2
    @6
    @47
    wceq
    @7
    @49
    @35
    @50
    @6
    @47
    @5
    eleq2
    @6
    @47
    @34
    sseq1
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    ralrimiva
    @25
    @13
    @37
    vc
    @10
    @34
    @25
    @10
    @20
    @23
    cin
    @34
    @8
    @20
    @9
    @23
    ineq12
    @19
    @22
    cA
    inindir
    syl6eqr
    #
    @25
    @12
    @36
    vw
    @2
    @25
    @11
    @35
    @7
    @25
    @10
    @34
    @6
    @52
    sseq2d
    anbi2d
    rexbidv
    raleqbidv
    syl5ibrcom
    rexlimdvva
    sylbid
    ralrimivv
    @2
    cvv
    wcel
    @3
    @15
    wb
    cB
    cA
    crest
    ovex
    va
    vb
    vc
    vw
    @2
    cvv
    isbasis2g
    ax-mp
    sylibr
    @0
    @1
    wn
    #
    wa
    @2
    c0
    ctb
    @53
    @2
    c0
    wceq
    @0
    cB
    cA
    crest
    crest
    cdm
    #
    wrel
    cvv
    cvv
    cxp
    #
    wrel
    cvv
    cvv
    relxp
    @54
    @55
    crest
    @55
    wfn
    @54
    @55
    wceq
    restfn
    @55
    crest
    fndm
    ax-mp
    releqi
    mpbir
    ovprc2
    adantl
    c0
    cfi
    cfv
    c0
    ctb
    fi0
    c0
    fibas
    eqeltrri
    syl6eqel
    pm2.61dan
end
