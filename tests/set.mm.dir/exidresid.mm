include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "cgi.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crn.mm"
include "wral.mm"
include "crio.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "resexg.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "gidval.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "cdm.mm"
include "exidreslem.mm"
include "simprd.mm"
include "exidres.mm"
include "elin.mm"
include "rngopidOLD.mm"
include "sylbir.mm"
include "ancoms.mm"
include "sylan.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "wreu.mm"
include "wb.mm"
include "simpld.mm"
include "eleqtrrd.mm"
include "exidu1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem exidresid
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vu: setvar u
  assume exidres.1: |- X = ran G
  assume exidres.2: |- U = ( GId ` G )
  assume exidres.3: |- H = ( G |` ( Y X. Y ) )


  assert |- ( ( ( G e. ( Magma i^i ExId ) /\ Y C_ X /\ U e. Y ) /\ H e. Magma ) -> ( GId ` H ) = U )

  proof
    cG
    cmagm
    cexid
    cin
    #
    wcel
    #
    cY
    cX
    wss
    #
    cU
    cY
    wcel
    #
    w3a
    #
    cH
    cmagm
    wcel
    #
    wa
    #
    cH
    cgi
    cfv
    #
    vu
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    @9
    wceq
    #
    @9
    @8
    cH
    co
    #
    @9
    wceq
    #
    wa
    #
    vx
    cH
    crn
    #
    wral
    #
    vu
    @15
    crio
    #
    cU
    @4
    @7
    @17
    wceq
    #
    @5
    @1
    @2
    @18
    @3
    @1
    cH
    cvv
    wcel
    @18
    @1
    cH
    cG
    cY
    cY
    cxp
    #
    cres
    cvv
    exidres.3
    cG
    @19
    @0
    resexg
    syl5eqel
    vx
    vu
    cH
    cvv
    @15
    @15
    eqid
    #
    gidval
    syl
    3ad2ant1
    adantr
    @6
    cU
    @9
    cH
    co
    #
    @9
    wceq
    #
    @9
    cU
    cH
    co
    #
    @9
    wceq
    #
    wa
    #
    vx
    @15
    wral
    #
    @17
    cU
    wceq
    #
    @6
    @26
    @25
    vx
    cH
    cdm
    cdm
    #
    wral
    #
    @4
    @29
    @5
    @4
    cU
    @28
    wcel
    #
    @29
    vx
    cU
    cG
    cH
    cX
    cY
    exidres.1
    exidres.2
    exidres.3
    exidreslem
    #
    simprd
    adantr
    @6
    @25
    vx
    @15
    @28
    @4
    cH
    cexid
    wcel
    #
    @5
    @15
    @28
    wceq
    #
    cU
    cG
    cH
    cX
    cY
    exidres.1
    exidres.2
    exidres.3
    exidres
    #
    @5
    @32
    @33
    @5
    @32
    wa
    #
    cH
    @0
    wcel
    #
    @33
    cH
    cmagm
    cexid
    elin
    #
    cH
    rngopidOLD
    sylbir
    ancoms
    sylan
    #
    raleqdv
    mpbird
    @6
    cU
    @15
    wcel
    @16
    vu
    @15
    wreu
    #
    @26
    @27
    wb
    @6
    cU
    @28
    @15
    @4
    @30
    @5
    @4
    @30
    @29
    @31
    simpld
    adantr
    @38
    eleqtrrd
    @4
    @32
    @5
    @39
    @34
    @5
    @32
    @39
    @35
    @36
    @39
    @37
    vx
    vu
    cH
    @15
    @20
    exidu1
    sylbir
    ancoms
    sylan
    @16
    @26
    vu
    @15
    cU
    @8
    cU
    wceq
    #
    @14
    @25
    vx
    @15
    @40
    @11
    @22
    @13
    @24
    @40
    @10
    @21
    @9
    @8
    cU
    @9
    cH
    oveq1
    eqeq1d
    @40
    @12
    @23
    @9
    @8
    cU
    @9
    cH
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    riota2
    syl2anc
    mpbid
    eqtrd
end
