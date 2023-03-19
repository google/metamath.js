include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cafv.mm"
include "cfv.mm"
include "cdm.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wceq.mm"
include "fvco2.mm"
include "adantl.mm"
include "simpll.mm"
include "wb.mm"
include "df-fn.mm"
include "wi.mm"
include "eleq2.mm"
include "eqcoms.mm"
include "biimpd.mm"
include "imp.mm"
include "jca.mm"
include "sylanb.mm"
include "dmfco.mm"
include "syl.mm"
include "mpbird.mm"
include "funcoressn.mm"
include "wdfat.mm"
include "df-dfat.mm"
include "afvfundmfveq.mm"
include "sylbir.mm"
include "syl2anc.mm"
include "adantr.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "cvv.mm"
include "wo.mm"
include "ianor.mm"
include "funfni.mm"
include "bicomd.mm"
include "notbid.mm"
include "ndmafv.mm"
include "syl6com.mm"
include "funressnfv.mm"
include "ex.mm"
include "afvnfundmuv.mm"
include "sylnbir.mm"
include "nsyl4.mm"
include "com12.mm"
include "con1d.mm"
include "jaoi.mm"
include "sylbi.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "pm2.61ian.mm"
include "eqidd.mm"
include "fnfun.mm"
include "funres.mm"
include "afveq12d.mm"

theorem afvco2
  let cA: class A
  let cF: class F
  let cG: class G
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( G Fn A /\ X e. A ) -> ( ( F o. G ) ''' X ) = ( F ''' ( G ''' X ) ) )

  proof
    cG
    cA
    wfn
    #
    cX
    cA
    wcel
    #
    wa
    #
    cX
    cF
    cG
    ccom
    #
    cafv
    #
    cX
    cG
    cfv
    #
    cF
    cafv
    #
    cX
    cG
    cafv
    #
    cF
    cafv
    @5
    cF
    cdm
    wcel
    #
    cF
    @5
    csn
    cres
    wfun
    #
    wa
    #
    @2
    @4
    @6
    wceq
    @10
    @2
    wa
    #
    cX
    @3
    cfv
    #
    @5
    cF
    cfv
    #
    @4
    @6
    @2
    @12
    @13
    wceq
    @10
    cA
    cF
    cG
    cX
    fvco2
    adantl
    @11
    cX
    @3
    cdm
    wcel
    #
    @3
    cX
    csn
    #
    cres
    wfun
    #
    @4
    @12
    wceq
    #
    @11
    @14
    @8
    @8
    @9
    @2
    simpll
    @11
    cG
    wfun
    #
    cX
    cG
    cdm
    #
    wcel
    #
    wa
    #
    @14
    @8
    wb
    #
    @2
    @21
    @10
    @0
    @18
    @19
    cA
    wceq
    #
    wa
    #
    @1
    @21
    cG
    cA
    df-fn
    #
    @24
    @1
    wa
    @18
    @20
    @18
    @23
    @1
    simpll
    @24
    @1
    @20
    @23
    @1
    @20
    wi
    #
    @18
    @23
    @1
    @20
    @1
    @20
    wb
    cA
    @19
    cA
    @19
    cX
    eleq2
    eqcoms
    biimpd
    adantl
    #
    imp
    jca
    sylanb
    adantl
    cX
    cF
    cG
    dmfco
    #
    syl
    mpbird
    cA
    cF
    cG
    cX
    funcoressn
    @14
    @16
    wa
    #
    cX
    @3
    wdfat
    #
    @17
    cX
    @3
    df-dfat
    #
    cX
    @3
    afvfundmfveq
    sylbir
    syl2anc
    @10
    @6
    @13
    wceq
    #
    @2
    @10
    @5
    cF
    wdfat
    #
    @32
    @5
    cF
    df-dfat
    #
    @5
    cF
    afvfundmfveq
    sylbir
    adantr
    3eqtr4d
    @10
    wn
    #
    @2
    wa
    @4
    cvv
    @6
    @35
    @2
    @4
    cvv
    wceq
    #
    @35
    @8
    wn
    #
    @9
    wn
    #
    wo
    @2
    @36
    wi
    #
    @8
    @9
    ianor
    @37
    @39
    @38
    @2
    @37
    @14
    wn
    #
    @36
    @2
    @37
    @40
    @2
    @8
    @14
    @2
    @14
    @8
    @22
    cA
    cX
    cG
    @28
    funfni
    bicomd
    notbid
    biimpd
    cX
    @3
    ndmafv
    syl6com
    @2
    @38
    @36
    @2
    @36
    @9
    @36
    wn
    @2
    @9
    @29
    @2
    @9
    wi
    @36
    @29
    @2
    @9
    cA
    cF
    cG
    cX
    funressnfv
    ex
    @29
    @30
    @36
    @31
    cX
    @3
    afvnfundmuv
    sylnbir
    nsyl4
    com12
    con1d
    com12
    jaoi
    sylbi
    imp
    @35
    cvv
    @6
    wceq
    @2
    @35
    @6
    cvv
    @10
    @33
    @6
    cvv
    wceq
    @34
    @5
    cF
    afvnfundmuv
    sylnbir
    eqcomd
    adantr
    eqtrd
    pm2.61ian
    @2
    @5
    @7
    cF
    cF
    @2
    cF
    eqidd
    @2
    @7
    @5
    @2
    @20
    cG
    @15
    cres
    wfun
    #
    @7
    @5
    wceq
    #
    @0
    @1
    @20
    @0
    @24
    @26
    @25
    @27
    sylbi
    imp
    @0
    @41
    @1
    @0
    @18
    @41
    cA
    cG
    fnfun
    @15
    cG
    funres
    syl
    adantr
    @20
    @41
    wa
    cX
    cG
    wdfat
    @42
    cX
    cG
    df-dfat
    cX
    cG
    afvfundmfveq
    sylbir
    syl2anc
    eqcomd
    afveq12d
    eqtrd
end
