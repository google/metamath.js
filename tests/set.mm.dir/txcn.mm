include "ctop.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "ccom.mm"
include "wa.mm"
include "wi.mm"
include "ctopon.mm"
include "cfv.mm"
include "toptopon.mm"
include "c1st.mm"
include "cxp.mm"
include "cres.mm"
include "reseq2i.mm"
include "eqtri.mm"
include "tx1cn.mm"
include "syl5eqel.mm"
include "c2nd.mm"
include "tx2cn.mm"
include "cnco.mm"
include "anim12dan.mm"
include "expcom.mm"
include "syl2anc.mm"
include "syl2anb.mm"
include "3adant3.mm"
include "cv.mm"
include "wceq.mm"
include "weu.mm"
include "wex.mm"
include "cntop1.mm"
include "ad2antrl.mm"
include "topopn.mm"
include "syl.mm"
include "cnf.mm"
include "ad2antll.mm"
include "upxp.mm"
include "wb.mm"
include "feq3.mm"
include "ax-mp.mm"
include "3anbi1i.mm"
include "eubii.mm"
include "sylibr.mm"
include "syl3anc.mm"
include "euex.mm"
include "cvv.mm"
include "wmo.mm"
include "simpll3.mm"
include "adantr.mm"
include "xpexg.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "fex2.mm"
include "eumo.mm"
include "simpr.mm"
include "3anass.mm"
include "coeq2.mm"
include "jca.mm"
include "eqcoms.mm"
include "biantrud.mm"
include "feq1.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "moi2.mm"
include "syl22anc.mm"
include "wreu.mm"
include "eqid.mm"
include "uptx.mm"
include "adantl.mm"
include "df-reu.mm"
include "sylbi.mm"
include "cuni.mm"
include "txuni.mm"
include "syl5eq.mm"
include "feq3d.mm"
include "syl5ibr.mm"
include "anim1d.mm"
include "syl6ibr.mm"
include "simpl.mm"
include "a1i.mm"
include "jcad.mm"
include "eximdv.mm"
include "syl5.mm"
include "mpd.mm"
include "eupick.mm"
include "imp.mm"
include "eqeltrrd.mm"
include "exlimddv.mm"
include "ex.mm"
include "impbid.mm"

theorem txcn
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vh: setvar h
  assume txcn.1: |- X = U. R
  assume txcn.2: |- Y = U. S
  assume txcn.3: |- Z = ( X X. Y )
  assume txcn.4: |- W = U. U
  assume txcn.5: |- P = ( 1st |` Z )
  assume txcn.6: |- Q = ( 2nd |` Z )


  assert |- ( ( R e. Top /\ S e. Top /\ F : W --> Z ) -> ( F e. ( U Cn ( R tX S ) ) <-> ( ( P o. F ) e. ( U Cn R ) /\ ( Q o. F ) e. ( U Cn S ) ) ) )

  proof
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    cW
    cZ
    cF
    wf
    #
    w3a
    #
    cF
    cU
    cR
    cS
    ctx
    co
    #
    ccn
    co
    #
    wcel
    #
    cP
    cF
    ccom
    #
    cU
    cR
    ccn
    co
    wcel
    #
    cQ
    cF
    ccom
    #
    cU
    cS
    ccn
    co
    wcel
    #
    wa
    #
    @0
    @1
    @6
    @11
    wi
    #
    @2
    @0
    cR
    cX
    ctopon
    cfv
    wcel
    #
    cS
    cY
    ctopon
    cfv
    wcel
    #
    @12
    @1
    cR
    cX
    txcn.1
    toptopon
    cS
    cY
    txcn.2
    toptopon
    @13
    @14
    wa
    #
    cP
    @4
    cR
    ccn
    co
    #
    wcel
    #
    cQ
    @4
    cS
    ccn
    co
    #
    wcel
    #
    @12
    @15
    cP
    c1st
    cX
    cY
    cxp
    #
    cres
    #
    @16
    cP
    c1st
    cZ
    cres
    @21
    txcn.5
    cZ
    @20
    c1st
    txcn.3
    reseq2i
    eqtri
    #
    cR
    cS
    cX
    cY
    tx1cn
    syl5eqel
    @15
    cQ
    c2nd
    @20
    cres
    #
    @18
    cQ
    c2nd
    cZ
    cres
    @23
    txcn.6
    cZ
    @20
    c2nd
    txcn.3
    reseq2i
    eqtri
    #
    cR
    cS
    cX
    cY
    tx2cn
    syl5eqel
    @6
    @17
    @19
    wa
    @11
    @6
    @17
    @8
    @19
    @10
    cF
    cP
    cU
    @4
    cR
    cnco
    cF
    cQ
    cU
    @4
    cS
    cnco
    anim12dan
    expcom
    syl2anc
    syl2anb
    3adant3
    @3
    @11
    @6
    @3
    @11
    wa
    #
    cW
    cZ
    vh
    cv
    #
    wf
    #
    @7
    cP
    @26
    ccom
    wceq
    #
    @9
    cQ
    @26
    ccom
    wceq
    #
    w3a
    #
    @6
    vh
    @25
    @30
    vh
    weu
    #
    @30
    vh
    wex
    @25
    cW
    cU
    wcel
    #
    cW
    cX
    @7
    wf
    #
    cW
    cY
    @9
    wf
    #
    @31
    @25
    cU
    ctop
    wcel
    #
    @32
    @8
    @35
    @3
    @10
    @7
    cU
    cR
    cntop1
    ad2antrl
    cU
    cW
    txcn.4
    topopn
    syl
    #
    @8
    @33
    @3
    @10
    @7
    cU
    cR
    cW
    cX
    txcn.4
    txcn.1
    cnf
    ad2antrl
    @10
    @34
    @3
    @8
    @9
    cU
    cS
    cW
    cY
    txcn.4
    txcn.2
    cnf
    ad2antll
    @32
    @33
    @34
    w3a
    cW
    @20
    @26
    wf
    #
    @28
    @29
    w3a
    #
    vh
    weu
    @31
    cW
    cX
    cY
    cU
    cP
    cQ
    vh
    @7
    @9
    @22
    @24
    upxp
    @30
    @38
    vh
    @27
    @37
    @28
    @29
    cZ
    @20
    wceq
    @27
    @37
    wb
    txcn.3
    cZ
    @20
    cW
    @26
    feq3
    ax-mp
    3anbi1i
    eubii
    sylibr
    syl3anc
    #
    @30
    vh
    euex
    syl
    @25
    @30
    wa
    #
    @26
    cF
    @5
    @40
    cF
    cvv
    wcel
    #
    @30
    vh
    wmo
    #
    @30
    @2
    @26
    cF
    wceq
    #
    @40
    @2
    @32
    cZ
    cvv
    wcel
    #
    @41
    @0
    @1
    @2
    @11
    @30
    simpll3
    #
    @25
    @32
    @30
    @36
    adantr
    @3
    @44
    @11
    @30
    @0
    @1
    @44
    @2
    @0
    cX
    cR
    wcel
    #
    cY
    cS
    wcel
    #
    @44
    @1
    cR
    cX
    txcn.1
    topopn
    cS
    cY
    txcn.2
    topopn
    @46
    @47
    wa
    cZ
    @20
    cvv
    txcn.3
    cX
    cY
    cR
    cS
    xpexg
    syl5eqel
    syl2an
    3adant3
    ad2antrr
    cW
    cZ
    cF
    cU
    cvv
    fex2
    syl3anc
    @25
    @42
    @30
    @25
    @31
    @42
    @39
    @30
    vh
    eumo
    syl
    adantr
    @25
    @30
    simpr
    @45
    @30
    @2
    vh
    cF
    cvv
    @30
    @27
    @28
    @29
    wa
    #
    wa
    #
    @43
    @2
    @27
    @28
    @29
    3anass
    #
    @43
    @27
    @49
    @2
    @43
    @48
    @27
    @48
    cF
    @26
    cF
    @26
    wceq
    @28
    @29
    cF
    @26
    cP
    coeq2
    cF
    @26
    cQ
    coeq2
    jca
    eqcoms
    biantrud
    cW
    cZ
    @26
    cF
    feq1
    bitr3d
    syl5bb
    moi2
    syl22anc
    @25
    @30
    @26
    @5
    wcel
    #
    @25
    @31
    @30
    @51
    wa
    #
    vh
    wex
    #
    @30
    @51
    wi
    @39
    @25
    @48
    vh
    @5
    wreu
    #
    @53
    @11
    @54
    @3
    cP
    cQ
    cR
    cS
    @4
    cU
    vh
    @7
    @9
    cX
    cY
    cZ
    @4
    eqid
    txcn.1
    txcn.2
    txcn.3
    txcn.5
    txcn.6
    uptx
    adantl
    @54
    @51
    @48
    wa
    #
    vh
    wex
    #
    @25
    @53
    @54
    @55
    vh
    weu
    @56
    @48
    vh
    @5
    df-reu
    @55
    vh
    euex
    sylbi
    @25
    @55
    @52
    vh
    @25
    @55
    @30
    @51
    @25
    @55
    @49
    @30
    @25
    @51
    @27
    @48
    @51
    @27
    @25
    cW
    @4
    cuni
    #
    @26
    wf
    @26
    cU
    @4
    cW
    @57
    txcn.4
    @57
    eqid
    cnf
    @25
    cZ
    @57
    @26
    cW
    @3
    cZ
    @57
    wceq
    #
    @11
    @0
    @1
    @58
    @2
    @0
    @1
    wa
    cZ
    @20
    @57
    txcn.3
    cR
    cS
    cX
    cY
    txcn.1
    txcn.2
    txuni
    syl5eq
    3adant3
    adantr
    feq3d
    syl5ibr
    anim1d
    @50
    syl6ibr
    @55
    @51
    wi
    @25
    @51
    @48
    simpl
    a1i
    jcad
    eximdv
    syl5
    mpd
    @30
    @51
    vh
    eupick
    syl2anc
    imp
    eqeltrrd
    exlimddv
    ex
    impbid
end
