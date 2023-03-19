include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cupgr.mm"
include "wcel.mm"
include "cupwlks.mm"
include "cvv.mm"
include "w3a.mm"
include "wlkv.mm"
include "wa.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "csn.mm"
include "wss.mm"
include "wif.mm"
include "wi.mm"
include "eqid.mm"
include "iswlk.mm"
include "simpr1.mm"
include "simpr2.mm"
include "wn.mm"
include "wo.mm"
include "df-ifp.mm"
include "dfsn2.mm"
include "preq2.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "a1d.mm"
include "cedg.mm"
include "simpr.mm"
include "simpl.mm"
include "upgredginwlk.mm"
include "syl2anr.mm"
include "imp.mm"
include "wne.mm"
include "simprr.mm"
include "adantr.mm"
include "simplr.mm"
include "df-ne.mm"
include "fvexd.mm"
include "id.mm"
include "3jca.mm"
include "sylbir.mm"
include "adantl.mm"
include "upgredgpr.mm"
include "syl31anc.mm"
include "eqcomd.mm"
include "exp31.mm"
include "mpd.mm"
include "com12.mm"
include "jaoi.mm"
include "syl5bi.mm"
include "ralimdva.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "impcom.mm"
include "sylbid.mm"
include "impd.mm"
include "wb.mm"
include "isupwlk.mm"
include "mpbird.mm"
include "mpid.mm"

theorem upgrwlkupwlk
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( G e. UPGraph /\ F ( Walks ` G ) P ) -> F ( UPWalks ` G ) P )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cupwlks
    cfv
    wbr
    #
    @0
    @1
    cG
    cvv
    wcel
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    w3a
    #
    @2
    cP
    cF
    cG
    wlkv
    @0
    @1
    @3
    @2
    @0
    @1
    wa
    #
    @3
    wa
    @2
    cF
    cG
    ciedg
    cfv
    #
    cdm
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
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
    cF
    cfv
    @5
    cfv
    #
    @10
    cP
    cfv
    #
    @10
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    vk
    cc0
    @7
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @3
    @4
    @19
    @3
    @0
    @1
    @19
    @3
    @0
    @6
    @9
    @12
    @14
    wceq
    #
    @11
    @12
    csn
    #
    wceq
    #
    @15
    @11
    wss
    #
    wif
    #
    vk
    @17
    wral
    #
    w3a
    #
    @1
    @19
    wi
    cP
    cvv
    vk
    cF
    cG
    @5
    @8
    cvv
    cvv
    @8
    eqid
    #
    @5
    eqid
    #
    iswlk
    @3
    @1
    @26
    @19
    @3
    @1
    @26
    @19
    @3
    @1
    wa
    #
    @26
    wa
    @6
    @9
    @18
    @29
    @6
    @9
    @25
    simpr1
    @29
    @6
    @9
    @25
    simpr2
    @26
    @29
    @18
    @6
    @9
    @25
    @29
    @18
    wi
    @6
    @9
    wa
    #
    @29
    @25
    @18
    @30
    @29
    @25
    @18
    wi
    @30
    @29
    wa
    #
    @24
    @16
    vk
    @17
    @24
    @20
    @22
    wa
    #
    @20
    wn
    #
    @23
    wa
    #
    wo
    #
    @31
    @10
    @17
    wcel
    #
    wa
    #
    @16
    @20
    @22
    @23
    df-ifp
    @35
    @37
    @16
    @32
    @37
    @16
    wi
    @34
    @32
    @16
    @37
    @20
    @22
    @16
    @20
    @21
    @15
    @11
    @20
    @21
    @12
    @12
    cpr
    @15
    @12
    dfsn2
    @12
    @14
    @12
    preq2
    syl5eq
    eqeq2d
    biimpa
    a1d
    @37
    @34
    @16
    @37
    @11
    cG
    cedg
    cfv
    #
    wcel
    #
    @34
    @16
    wi
    @31
    @36
    @39
    @29
    @1
    @6
    @36
    @39
    wi
    @30
    @3
    @1
    simpr
    @6
    @9
    simpl
    @38
    cF
    cG
    @5
    @10
    @28
    @38
    eqid
    #
    upgredginwlk
    syl2anr
    imp
    @37
    @39
    @34
    @16
    @37
    @39
    wa
    #
    @34
    wa
    #
    @15
    @11
    @42
    @1
    @39
    @23
    @12
    cvv
    wcel
    #
    @14
    cvv
    wcel
    #
    @12
    @14
    wne
    #
    w3a
    #
    @15
    @11
    wceq
    @41
    @1
    @34
    @37
    @1
    @39
    @31
    @1
    @36
    @30
    @3
    @1
    simprr
    adantr
    adantr
    adantr
    @37
    @39
    @34
    simplr
    @41
    @33
    @23
    simprr
    @34
    @46
    @41
    @33
    @46
    @23
    @33
    @45
    @46
    @12
    @14
    df-ne
    @45
    @43
    @44
    @45
    @45
    @10
    cP
    fvexd
    @45
    @13
    cP
    fvexd
    @45
    id
    3jca
    sylbir
    adantr
    adantl
    @12
    @14
    @11
    cvv
    @38
    cG
    @8
    cvv
    @27
    @40
    upgredgpr
    syl31anc
    eqcomd
    exp31
    mpd
    com12
    jaoi
    com12
    syl5bi
    ralimdva
    ex
    com23
    3impia
    impcom
    3jca
    exp31
    com23
    sylbid
    impd
    impcom
    @3
    @2
    @19
    wb
    @4
    cP
    cvv
    vk
    cF
    cG
    @5
    @8
    cvv
    cvv
    @27
    @28
    isupwlk
    adantl
    mpbird
    exp31
    mpid
    impcom
end
