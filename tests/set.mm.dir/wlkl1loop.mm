include "ciedg.mm"
include "cfv.mm"
include "wfun.mm"
include "cwlks.mm"
include "wbr.mm"
include "wa.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "csn.mm"
include "cedg.mm"
include "wcel.mm"
include "wi.mm"
include "cvv.mm"
include "w3a.mm"
include "wlkv.mm"
include "crn.mm"
include "cfzo.mm"
include "co.mm"
include "simp3l.mm"
include "simp2.mm"
include "c0ex.mm"
include "snid.mm"
include "oveq2.mm"
include "fzo01.mm"
include "syl6eq.mm"
include "syl5eleqr.mm"
include "ad2antrl.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "iedginwlk.mm"
include "syl3anc.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "caddc.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "wral.mm"
include "iswlkg.mm"
include "wb.mm"
include "raleqdv.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "wkslem2.mm"
include "mpdan.mm"
include "ralsn.mm"
include "syl6bb.mm"
include "ifptru.mm"
include "biimpa.mm"
include "eqcomd.mm"
include "ex.mm"
include "ad2antll.mm"
include "sylbid.mm"
include "com12.mm"
include "syl6bi.mm"
include "3imp.mm"
include "edgval.mm"
include "a1i.mm"
include "3eltr4d.mm"
include "3exp.mm"
include "3ad2ant1.mm"
include "mpcom.mm"
include "expd.mm"
include "impcom.mm"
include "imp.mm"

theorem wlkl1loop
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k


  assert |- ( ( ( Fun ( iEdg ` G ) /\ F ( Walks ` G ) P ) /\ ( ( # ` F ) = 1 /\ ( P ` 0 ) = ( P ` 1 ) ) ) -> { ( P ` 0 ) } e. ( Edg ` G ) )

  proof
    cG
    ciedg
    cfv
    #
    wfun
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    wa
    cF
    chash
    cfv
    #
    c1
    wceq
    #
    cc0
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    wceq
    #
    wa
    #
    @5
    csn
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    @2
    @1
    @8
    @11
    wi
    @2
    @1
    @8
    @11
    cG
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    w3a
    @2
    @1
    @8
    wa
    #
    @11
    wi
    #
    cP
    cF
    cG
    wlkv
    @12
    @13
    @2
    @16
    wi
    @14
    @12
    @2
    @15
    @11
    @12
    @2
    @15
    w3a
    #
    cc0
    cF
    cfv
    @0
    cfv
    #
    @0
    crn
    #
    @9
    @10
    @17
    @1
    @2
    cc0
    cc0
    @3
    cfzo
    co
    #
    wcel
    #
    @18
    @19
    wcel
    @12
    @2
    @1
    @8
    simp3l
    @12
    @2
    @15
    simp2
    @15
    @12
    @21
    @2
    @4
    @21
    @1
    @7
    @4
    cc0
    cc0
    csn
    #
    @20
    cc0
    c0ex
    snid
    @4
    @20
    cc0
    c1
    cfzo
    co
    @22
    @3
    c1
    cc0
    cfzo
    oveq2
    fzo01
    syl6eq
    #
    syl5eleqr
    ad2antrl
    3ad2ant3
    cP
    cF
    cG
    @0
    cc0
    @0
    eqid
    #
    iedginwlk
    syl3anc
    @12
    @2
    @15
    @9
    @18
    wceq
    #
    @12
    @2
    cF
    @0
    cdm
    cword
    wcel
    #
    cc0
    @3
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    vk
    cv
    #
    cP
    cfv
    #
    @29
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    @29
    cF
    cfv
    @0
    cfv
    #
    @30
    csn
    wceq
    @30
    @32
    cpr
    @33
    wss
    wif
    #
    vk
    @20
    wral
    #
    w3a
    @15
    @25
    wi
    #
    cP
    vk
    cF
    cG
    @0
    @27
    cvv
    @27
    eqid
    @24
    iswlkg
    @35
    @26
    @36
    @28
    @15
    @35
    @25
    @15
    @35
    @7
    @18
    @9
    wceq
    #
    @5
    @6
    cpr
    @18
    wss
    #
    wif
    #
    @25
    @4
    @35
    @39
    wb
    @1
    @7
    @4
    @35
    @34
    vk
    @22
    wral
    @39
    @4
    @34
    vk
    @20
    @22
    @23
    raleqdv
    @34
    @39
    vk
    cc0
    c0ex
    @29
    cc0
    wceq
    #
    @31
    c1
    wceq
    @34
    @39
    wb
    @40
    @31
    cc0
    c1
    caddc
    co
    c1
    @29
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    @29
    cc0
    c1
    cP
    cF
    @0
    wkslem2
    mpdan
    ralsn
    syl6bb
    ad2antrl
    @7
    @39
    @25
    wi
    @1
    @4
    @7
    @39
    @25
    @7
    @39
    wa
    @18
    @9
    @7
    @39
    @37
    @7
    @37
    @38
    ifptru
    biimpa
    eqcomd
    ex
    ad2antll
    sylbid
    com12
    3ad2ant3
    syl6bi
    3imp
    @10
    @19
    wceq
    @17
    cG
    edgval
    a1i
    3eltr4d
    3exp
    3ad2ant1
    mpcom
    expd
    impcom
    imp
end
