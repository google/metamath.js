include "crngo.mm"
include "wcel.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "rngo0cl.mm"
include "wa.mm"
include "csn.mm"
include "en1eqsn.mm"
include "crn.mm"
include "c1st.mm"
include "cfv.mm"
include "rneqi.mm"
include "rngo1cl.mm"
include "eleq2.mm"
include "biimpd.mm"
include "elsni.mm"
include "syl6com.mm"
include "eqcomi.mm"
include "eleq2s.mm"
include "syl.mm"
include "syl5com.mm"
include "ex.mm"
include "com23.mm"
include "mpcom.mm"
include "c0.mm"
include "wne.mm"
include "rngone0.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "oveq2.mm"
include "ralrimivw.mm"
include "rngorz.mm"
include "ralrimiva.mm"
include "eqtri.mm"
include "rngoridm.mm"
include "r19.26.mm"
include "eqtr.mm"
include "eqcoms.mm"
include "imp31.mm"
include "ralimi.mm"
include "eqsn.mm"
include "ensn1g.mm"
include "breq1.mm"
include "syl5ibr.mm"
include "syl6bir.mm"
include "com3l.mm"
include "sylbir.mm"
include "com24.mm"
include "mpd.mm"
include "com13.mm"
include "impbid.mm"

theorem rngoueqz
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  assume uznzr.1: |- G = ( 1st ` R )
  assume uznzr.2: |- H = ( 2nd ` R )
  assume uznzr.3: |- Z = ( GId ` G )
  assume uznzr.4: |- U = ( GId ` H )
  assume uznzr.5: |- X = ran G


  assert |- ( R e. RingOps -> ( X ~~ 1o <-> U = Z ) )

  proof
    cR
    crngo
    wcel
    #
    cX
    c1o
    cen
    wbr
    #
    cU
    cZ
    wceq
    #
    cZ
    cX
    wcel
    #
    @0
    @1
    @2
    wi
    cR
    cG
    cX
    cZ
    uznzr.1
    uznzr.5
    uznzr.3
    rngo0cl
    #
    @3
    @1
    @0
    @2
    @3
    @1
    @0
    @2
    wi
    @3
    @1
    wa
    cX
    cZ
    csn
    #
    wceq
    #
    @0
    @2
    cZ
    cX
    en1eqsn
    @0
    cU
    cG
    crn
    #
    wcel
    @6
    @2
    wi
    #
    cR
    cU
    cH
    @7
    cG
    cR
    c1st
    cfv
    #
    uznzr.1
    rneqi
    #
    uznzr.2
    uznzr.4
    rngo1cl
    @8
    cU
    cX
    @7
    @6
    cU
    cX
    wcel
    #
    cU
    @5
    wcel
    #
    @2
    @6
    @11
    @12
    cX
    @5
    cU
    eleq2
    biimpd
    cU
    cZ
    elsni
    syl6com
    cX
    @7
    uznzr.5
    eqcomi
    eleq2s
    syl
    syl5com
    ex
    com23
    mpcom
    cX
    c0
    wne
    #
    @0
    @2
    @1
    wi
    cR
    cG
    cX
    uznzr.1
    uznzr.5
    rngone0
    @2
    @0
    @13
    @1
    @2
    vx
    cv
    #
    cU
    cH
    co
    #
    @14
    cZ
    cH
    co
    #
    wceq
    #
    vx
    cX
    wral
    #
    @0
    @13
    @1
    wi
    #
    @2
    @17
    vx
    cX
    cU
    cZ
    @14
    cH
    oveq2
    ralrimivw
    @0
    @16
    cZ
    wceq
    #
    vx
    cX
    wral
    #
    @18
    @19
    wi
    #
    @0
    @20
    vx
    cX
    @14
    cR
    cG
    cH
    cX
    cZ
    uznzr.3
    uznzr.5
    uznzr.1
    uznzr.2
    rngorz
    ralrimiva
    @15
    @14
    wceq
    #
    vx
    cX
    wral
    #
    @0
    @21
    @22
    wi
    @0
    @23
    vx
    cX
    @14
    cR
    cU
    cH
    cX
    uznzr.2
    cX
    @7
    @9
    crn
    uznzr.5
    @10
    eqtri
    uznzr.4
    rngoridm
    ralrimiva
    @24
    @18
    @21
    @0
    @19
    @24
    @18
    @21
    @0
    @19
    wi
    #
    wi
    #
    @24
    @18
    wa
    @23
    @17
    wa
    #
    vx
    cX
    wral
    #
    @26
    @23
    @17
    vx
    cX
    r19.26
    @28
    @21
    @25
    @28
    @21
    wa
    @27
    @20
    wa
    #
    vx
    cX
    wral
    #
    @25
    @27
    @20
    vx
    cX
    r19.26
    @30
    @14
    cZ
    wceq
    #
    vx
    cX
    wral
    #
    @25
    @29
    @31
    vx
    cX
    @23
    @17
    @20
    @31
    @17
    @20
    @31
    wi
    #
    wi
    @14
    @15
    @14
    @15
    wceq
    #
    @17
    @33
    @34
    @17
    wa
    @14
    @16
    wceq
    #
    @33
    @14
    @15
    @16
    eqtr
    @35
    @20
    @31
    @14
    @16
    cZ
    eqtr
    ex
    syl
    ex
    eqcoms
    imp31
    ralimi
    @13
    @32
    @0
    @1
    @13
    @32
    @6
    @0
    @1
    wi
    vx
    cX
    cZ
    eqsn
    @0
    @1
    @6
    @5
    c1o
    cen
    wbr
    #
    @0
    @3
    @36
    @4
    cZ
    cX
    ensn1g
    syl
    cX
    @5
    c1o
    cen
    breq1
    syl5ibr
    syl6bir
    com3l
    syl
    sylbir
    ex
    sylbir
    ex
    com24
    mpcom
    mpd
    syl5com
    com13
    mpcom
    impbid
end
