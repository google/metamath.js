include "ckgen.mm"
include "crn.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "ctop.mm"
include "wrex.mm"
include "wss.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "kgenf.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "mp2b.mm"
include "wa.mm"
include "cuni.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cin.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "ctopon.mm"
include "eqid.mm"
include "toptopon.mm"
include "kgentopon.mm"
include "sylbi.mm"
include "syl.mm"
include "toponss.mm"
include "sylan.mm"
include "simplr.mm"
include "kgencmp2.mm"
include "biimpa.mm"
include "ad2ant2rl.mm"
include "kgeni.mm"
include "syl2anc.mm"
include "kgencmp.mm"
include "eleqtrrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "simpl.mm"
include "sylib.mm"
include "elkgen.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"
include "fveq2.mm"
include "id.mm"
include "sseq12d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "kgentop.mm"
include "kgenss.mm"
include "eqssd.mm"

theorem kgenidm
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cK: class K


  assert |- ( J e. ran kGen -> ( kGen ` J ) = J )

  proof
    cJ
    ckgen
    crn
    wcel
    #
    cJ
    ckgen
    cfv
    #
    cJ
    @0
    vj
    cv
    #
    ckgen
    cfv
    #
    cJ
    wceq
    #
    vj
    ctop
    wrex
    #
    @1
    cJ
    wss
    #
    ctop
    ctop
    ckgen
    wf
    ckgen
    ctop
    wfn
    @0
    @5
    wb
    kgenf
    ctop
    ctop
    ckgen
    ffn
    vj
    ctop
    cJ
    ckgen
    fvelrnb
    mp2b
    @4
    @6
    vj
    ctop
    @2
    ctop
    wcel
    #
    @3
    ckgen
    cfv
    #
    @3
    wss
    @4
    @6
    @7
    vx
    @8
    @3
    @7
    vx
    cv
    #
    @8
    wcel
    #
    @9
    @3
    wcel
    #
    @7
    @10
    wa
    #
    @11
    @9
    @2
    cuni
    #
    wss
    #
    @2
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    @9
    @15
    cin
    #
    @16
    wcel
    #
    wi
    #
    vk
    @13
    cpw
    #
    wral
    #
    @7
    @8
    @13
    ctopon
    cfv
    #
    wcel
    #
    @10
    @14
    @7
    @3
    @23
    wcel
    #
    @24
    @7
    @2
    @23
    wcel
    #
    @25
    @2
    @13
    @13
    eqid
    toptopon
    #
    @2
    @13
    kgentopon
    sylbi
    @3
    @13
    kgentopon
    syl
    @9
    @8
    @13
    toponss
    sylan
    @12
    @20
    vk
    @21
    @12
    @15
    @21
    wcel
    #
    @17
    @19
    @12
    @28
    @17
    wa
    #
    wa
    #
    @18
    @3
    @15
    crest
    co
    #
    @16
    @30
    @10
    @31
    ccmp
    wcel
    #
    @18
    @31
    wcel
    @7
    @10
    @29
    simplr
    @7
    @17
    @32
    @10
    @28
    @7
    @17
    @32
    @2
    @15
    kgencmp2
    biimpa
    ad2ant2rl
    @9
    @3
    @15
    kgeni
    syl2anc
    @7
    @17
    @16
    @31
    wceq
    @10
    @28
    @2
    @15
    kgencmp
    ad2ant2rl
    eleqtrrd
    expr
    ralrimiva
    @12
    @26
    @11
    @14
    @22
    wa
    wb
    @12
    @7
    @26
    @7
    @10
    simpl
    @27
    sylib
    @9
    vk
    @2
    @13
    elkgen
    syl
    mpbir2and
    ex
    ssrdv
    @4
    @8
    @1
    @3
    cJ
    @3
    cJ
    ckgen
    fveq2
    @4
    id
    sseq12d
    syl5ibcom
    rexlimiv
    sylbi
    @0
    cJ
    ctop
    wcel
    cJ
    @1
    wss
    cJ
    kgentop
    cJ
    kgenss
    syl
    eqssd
end
