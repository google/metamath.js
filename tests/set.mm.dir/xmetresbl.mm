include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cxp.mm"
include "cres.mm"
include "cr.mm"
include "wf.mm"
include "cme.mm"
include "wss.mm"
include "simp1.mm"
include "cbl.mm"
include "co.mm"
include "blssm.mm"
include "syl5eqss.mm"
include "xmetres2.mm"
include "syl2anc.mm"
include "wfn.mm"
include "cv.mm"
include "wral.mm"
include "xmetf.mm"
include "syl.mm"
include "xpss12.mm"
include "fssresd.mm"
include "ffn.mm"
include "wa.mm"
include "wceq.mm"
include "ovres.mm"
include "adantl.mm"
include "ccnv.mm"
include "cima.mm"
include "wbr.mm"
include "wer.mm"
include "simpl1.mm"
include "eqid.mm"
include "xmeter.mm"
include "cec.mm"
include "blssec.mm"
include "sselda.mm"
include "adantrr.mm"
include "wb.mm"
include "simpl2.mm"
include "elecg.mm"
include "mpbid.mm"
include "adantrl.mm"
include "ertr3d.mm"
include "xmeterval.mm"
include "simp3d.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "sylanbrc.mm"
include "ismet2.mm"

theorem xmetresbl
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume xmetresbl.1: |- B = ( P ( ball ` D ) R )


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> ( D |` ( B X. B ) ) e. ( Met ` B ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    w3a
    #
    cD
    cB
    cB
    cxp
    #
    cres
    #
    cB
    cxmt
    cfv
    wcel
    #
    @4
    cr
    @5
    wf
    #
    @5
    cB
    cme
    cfv
    wcel
    @3
    @0
    cB
    cX
    wss
    #
    @6
    @0
    @1
    @2
    simp1
    #
    @3
    cB
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    cX
    xmetresbl.1
    cD
    cP
    cR
    cX
    blssm
    syl5eqss
    #
    cD
    cB
    cX
    xmetres2
    syl2anc
    @3
    @5
    @4
    wfn
    #
    vx
    cv
    #
    vy
    cv
    #
    @5
    co
    #
    cr
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @7
    @3
    @4
    cxr
    @5
    wf
    @12
    @3
    cX
    cX
    cxp
    #
    cxr
    @4
    cD
    @3
    @0
    @17
    cxr
    cD
    wf
    @9
    cD
    cX
    xmetf
    syl
    @3
    @8
    @8
    @4
    @17
    wss
    @11
    @11
    cB
    cX
    cB
    cX
    xpss12
    syl2anc
    fssresd
    @4
    cxr
    @5
    ffn
    syl
    @3
    @16
    vx
    vy
    cB
    cB
    @3
    @13
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    wa
    #
    wa
    #
    @15
    @13
    @14
    cD
    co
    #
    cr
    @20
    @15
    @22
    wceq
    @3
    @13
    @14
    cB
    cB
    cD
    ovres
    adantl
    @21
    @13
    cX
    wcel
    #
    @14
    cX
    wcel
    #
    @22
    cr
    wcel
    #
    @21
    @13
    @14
    cD
    ccnv
    cr
    cima
    #
    wbr
    #
    @23
    @24
    @25
    w3a
    #
    @21
    @13
    cP
    @14
    @26
    cX
    @21
    @0
    cX
    @26
    wer
    @0
    @1
    @2
    @20
    simpl1
    #
    cD
    @26
    cX
    @26
    eqid
    #
    xmeter
    syl
    @21
    @13
    cP
    @26
    cec
    #
    wcel
    #
    cP
    @13
    @26
    wbr
    #
    @3
    @18
    @32
    @19
    @3
    cB
    @31
    @13
    @3
    cB
    @10
    @31
    xmetresbl.1
    cD
    cP
    @26
    cR
    cX
    @30
    blssec
    syl5eqss
    #
    sselda
    adantrr
    #
    @21
    @32
    @1
    @32
    @33
    wb
    @35
    @0
    @1
    @2
    @20
    simpl2
    #
    @13
    cP
    @26
    @31
    cX
    elecg
    syl2anc
    mpbid
    @21
    @14
    @31
    wcel
    #
    cP
    @14
    @26
    wbr
    #
    @3
    @19
    @37
    @18
    @3
    cB
    @31
    @14
    @34
    sselda
    adantrl
    #
    @21
    @37
    @1
    @37
    @38
    wb
    @39
    @36
    @14
    cP
    @26
    @31
    cX
    elecg
    syl2anc
    mpbid
    ertr3d
    @21
    @0
    @27
    @28
    wb
    @29
    @13
    @14
    cD
    @26
    cX
    @30
    xmeterval
    syl
    mpbid
    simp3d
    eqeltrd
    ralrimivva
    vx
    vy
    cB
    cB
    cr
    @5
    ffnov
    sylanbrc
    @5
    cB
    ismet2
    sylanbrc
end
