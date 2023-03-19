include "wf1.mm"
include "wa.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wi.mm"
include "f1cocnv1.mm"
include "coeq2.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "adantr.mm"
include "wfn.mm"
include "f1fn.mm"
include "adantl.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "cfv.mm"
include "equid.mm"
include "resieq.mm"
include "mpbiri.mm"
include "anidms.mm"
include "wb.mm"
include "breq.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "wex.mm"
include "cop.mm"
include "wfun.mm"
include "cdm.mm"
include "fnfun.mm"
include "syl.mm"
include "fndm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "funopfvb.mm"
include "syl2anc.mm"
include "bicomd.mm"
include "df-br.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "biimpd.mm"
include "syl6rbbr.mm"
include "vex.mm"
include "brcnv.mm"
include "anim12d.mm"
include "eximdv.mm"
include "brco.mm"
include "fvex.mm"
include "eqvinc.mm"
include "3imtr4g.mm"
include "adantlr.mm"
include "mpd.mm"
include "eqfnfvd.mm"
include "eqcomd.mm"
include "ex.mm"
include "impbid.mm"

theorem f1eqcocnv
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A -1-1-> B /\ G : A -1-1-> B ) -> ( F = G <-> ( `' F o. G ) = ( _I |` A ) ) )

  proof
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cG
    wf1
    #
    wa
    #
    cF
    cG
    wceq
    #
    cF
    ccnv
    #
    cG
    ccom
    #
    cid
    cA
    cres
    #
    wceq
    #
    @0
    @3
    @7
    wi
    @1
    @0
    @4
    cF
    ccom
    #
    @6
    wceq
    @3
    @7
    cA
    cB
    cF
    f1cocnv1
    @3
    @8
    @5
    @6
    cF
    cG
    @4
    coeq2
    eqeq1d
    syl5ibcom
    adantr
    @2
    @7
    @3
    @2
    @7
    wa
    #
    cG
    cF
    @9
    vx
    cA
    cG
    cF
    @2
    cG
    cA
    wfn
    #
    @7
    @1
    @10
    @0
    cA
    cB
    cG
    f1fn
    adantl
    #
    adantr
    @2
    cF
    cA
    wfn
    #
    @7
    @0
    @12
    @1
    cA
    cB
    cF
    f1fn
    adantr
    #
    adantr
    @9
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @14
    @14
    @5
    wbr
    #
    @14
    cG
    cfv
    #
    @14
    cF
    cfv
    #
    wceq
    #
    @16
    @17
    @14
    @14
    @6
    wbr
    #
    @15
    @21
    @9
    @15
    @21
    @15
    @15
    wa
    @21
    @14
    @14
    wceq
    vx
    equid
    cA
    @14
    @14
    resieq
    mpbiri
    anidms
    adantl
    @7
    @17
    @21
    wb
    @2
    @15
    @14
    @14
    @5
    @6
    breq
    ad2antlr
    mpbird
    @2
    @15
    @17
    @20
    wi
    @7
    @2
    @15
    wa
    #
    @14
    vy
    cv
    #
    cG
    wbr
    #
    @23
    @14
    @4
    wbr
    #
    wa
    #
    vy
    wex
    @23
    @18
    wceq
    #
    @23
    @19
    wceq
    #
    wa
    #
    vy
    wex
    @17
    @20
    @22
    @26
    @29
    vy
    @22
    @24
    @27
    @25
    @28
    @22
    @24
    @27
    @22
    @14
    @23
    cop
    #
    cG
    wcel
    #
    @18
    @23
    wceq
    #
    @24
    @27
    @22
    @32
    @31
    @22
    cG
    wfun
    #
    @14
    cG
    cdm
    #
    wcel
    #
    @32
    @31
    wb
    @2
    @33
    @15
    @2
    @10
    @33
    @11
    cA
    cG
    fnfun
    syl
    adantr
    @2
    @35
    @15
    @2
    @34
    cA
    @14
    @2
    @10
    @34
    cA
    wceq
    @11
    cA
    cG
    fndm
    syl
    eleq2d
    biimpar
    @14
    @23
    cG
    funopfvb
    syl2anc
    bicomd
    @14
    @23
    cG
    df-br
    @23
    @18
    eqcom
    3bitr4g
    biimpd
    @22
    @25
    @28
    @22
    @14
    @23
    cF
    wbr
    #
    @19
    @23
    wceq
    #
    @25
    @28
    @22
    @37
    @30
    cF
    wcel
    #
    @36
    @22
    cF
    wfun
    #
    @14
    cF
    cdm
    #
    wcel
    #
    @37
    @38
    wb
    @2
    @39
    @15
    @2
    @12
    @39
    @13
    cA
    cF
    fnfun
    syl
    adantr
    @2
    @41
    @15
    @2
    @40
    cA
    @14
    @2
    @12
    @40
    cA
    wceq
    @13
    cA
    cF
    fndm
    syl
    eleq2d
    biimpar
    @14
    @23
    cF
    funopfvb
    syl2anc
    @14
    @23
    cF
    df-br
    syl6rbbr
    @23
    @14
    cF
    vy
    vex
    vx
    vex
    #
    brcnv
    @23
    @19
    eqcom
    3bitr4g
    biimpd
    anim12d
    eximdv
    vy
    @14
    @14
    @4
    cG
    @42
    @42
    brco
    vy
    @18
    @19
    @14
    cG
    fvex
    eqvinc
    3imtr4g
    adantlr
    mpd
    eqfnfvd
    eqcomd
    ex
    impbid
end
