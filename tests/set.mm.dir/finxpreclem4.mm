include "com.mm"
include "wcel.mm"
include "c2o.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cvv.mm"
include "cxp.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "crdg.mm"
include "c1o.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "con0.mm"
include "crio.mm"
include "csuc.mm"
include "2onn.mm"
include "nnon.mm"
include "wsbc.mm"
include "wreu.mm"
include "2on.mm"
include "oawordeu.mm"
include "mpanl1.mm"
include "riotasbc.mm"
include "syl.mm"
include "csb.mm"
include "wb.mm"
include "riotaex.mm"
include "sbceq1g.mm"
include "ax-mp.mm"
include "csbov2g.mm"
include "csbvarg.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "eqeq1i.mm"
include "bitri.mm"
include "sylib.mm"
include "sylan.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "riotacl.mm"
include "wn.mm"
include "c0.mm"
include "riotaund.mm"
include "0elon.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"
include "nnarcl.mm"
include "mpan.mm"
include "biantrur.mm"
include "syl6bbr.mm"
include "nnacom.mm"
include "sylancr.mm"
include "df-2o.mm"
include "1onn.mm"
include "nnasuc.mm"
include "sylancl.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"
include "wne.mm"
include "wlim.mm"
include "adantr.mm"
include "sucidg.mm"
include "eleqtrri.mm"
include "ssel.mm"
include "mpi.mm"
include "ne0i.mm"
include "adantl.mm"
include "nnlim.mm"
include "onsucuni3.mm"
include "syl3anc.mm"
include "suceq.mm"
include "cfn.mm"
include "word.mm"
include "ordom.mm"
include "ordelss.mm"
include "nnfi.mm"
include "nnunifi.mm"
include "syl2anc.mm"
include "nnacl.mm"
include "peano4.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "finxpreclem3.mm"
include "df-1o.mm"
include "fveq2i.mm"
include "rdgsuc.mm"
include "opex.mm"
include "rdg0.mm"
include "3eqtri.mm"
include "syl6reqr.mm"
include "2on0.mm"
include "rdgsucuni.mm"
include "mp3an.mm"
include "1oequni2o.mm"
include "eqtr4i.mm"
include "3eqtr4g.mm"
include "wi.mm"
include "1on.mm"
include "rdgeqoa.mm"
include "mp3an12.mm"
include "sylc.mm"
include "3eqtr2rd.mm"

theorem finxpreclem4
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vo: setvar o
  assume finxpreclem4.1: |- F = ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) )

  disjoint N n
  disjoint N x
  disjoint n x
  disjoint U n
  disjoint U x
  disjoint n y
  disjoint x y
  disjoint N o
  assert |- ( ( ( N e. _om /\ 2o C_ N ) /\ y e. ( _V X. U ) ) -> ( rec ( F , <. N , y >. ) ` N ) = ( rec ( F , <. U. N , ( 1st ` y ) >. ) ` U. N ) )

  proof
    cN
    com
    wcel
    #
    c2o
    cN
    wss
    #
    wa
    #
    vy
    cv
    #
    cvv
    cU
    cxp
    wcel
    #
    wa
    #
    cN
    cuni
    #
    cF
    @6
    @3
    c1st
    cfv
    #
    cop
    #
    crdg
    #
    cfv
    #
    c1o
    c2o
    vo
    cv
    #
    coa
    co
    #
    cN
    wceq
    #
    vo
    con0
    crio
    #
    coa
    co
    #
    @9
    cfv
    #
    c2o
    @14
    coa
    co
    #
    cF
    cN
    @3
    cop
    #
    crdg
    #
    cfv
    #
    cN
    @19
    cfv
    #
    @2
    @10
    @16
    wceq
    @4
    @2
    @6
    @15
    @9
    @2
    @6
    csuc
    #
    @15
    csuc
    #
    wceq
    #
    @6
    @15
    wceq
    #
    @2
    cN
    @14
    c1o
    coa
    co
    #
    csuc
    #
    @22
    @23
    @2
    @17
    @14
    c2o
    coa
    co
    #
    cN
    @27
    @2
    c2o
    com
    wcel
    #
    @14
    com
    wcel
    #
    @17
    @28
    wceq
    2onn
    @2
    @17
    com
    wcel
    #
    @30
    @2
    @17
    cN
    com
    @0
    cN
    con0
    wcel
    #
    @1
    @17
    cN
    wceq
    #
    cN
    nnon
    #
    @32
    @1
    wa
    #
    @13
    vo
    @14
    wsbc
    #
    @33
    @35
    @13
    vo
    con0
    wreu
    #
    @36
    c2o
    con0
    wcel
    #
    @32
    @1
    @37
    2on
    vo
    c2o
    cN
    oawordeu
    mpanl1
    @13
    vo
    con0
    riotasbc
    syl
    @36
    vo
    @14
    @12
    csb
    #
    cN
    wceq
    #
    @33
    @14
    cvv
    wcel
    #
    @36
    @40
    wb
    @13
    vo
    con0
    riotaex
    #
    vo
    @14
    @12
    cN
    cvv
    sbceq1g
    ax-mp
    @39
    @17
    cN
    @39
    c2o
    vo
    @14
    @11
    csb
    #
    coa
    co
    #
    @17
    @41
    @39
    @44
    wceq
    @42
    vo
    @14
    c2o
    @11
    coa
    cvv
    csbov2g
    ax-mp
    @43
    @14
    c2o
    coa
    @41
    @43
    @14
    wceq
    @42
    vo
    @14
    cvv
    csbvarg
    ax-mp
    oveq2i
    eqtri
    eqeq1i
    bitri
    sylib
    sylan
    #
    @0
    @1
    simpl
    eqeltrd
    @14
    con0
    wcel
    #
    @31
    @30
    wb
    @37
    @46
    @13
    vo
    con0
    riotacl
    @37
    wn
    @14
    c0
    con0
    @13
    vo
    con0
    riotaund
    0elon
    syl6eqel
    pm2.61i
    @46
    @31
    @29
    @30
    wa
    #
    @30
    @38
    @46
    @31
    @47
    wb
    2on
    c2o
    @14
    nnarcl
    mpan
    @29
    @30
    2onn
    biantrur
    syl6bbr
    ax-mp
    sylib
    #
    c2o
    @14
    nnacom
    sylancr
    @45
    @2
    @28
    @14
    c1o
    csuc
    #
    coa
    co
    #
    @27
    c2o
    @49
    @14
    coa
    df-2o
    oveq2i
    @2
    @30
    c1o
    com
    wcel
    #
    @50
    @27
    wceq
    @48
    1onn
    @14
    c1o
    nnasuc
    sylancl
    syl5eq
    3eqtr3d
    @2
    @32
    cN
    c0
    wne
    #
    cN
    wlim
    wn
    #
    cN
    @22
    wceq
    @0
    @32
    @1
    @34
    adantr
    @1
    @52
    @0
    @1
    c1o
    cN
    wcel
    #
    @52
    @1
    c1o
    c2o
    wcel
    @54
    c1o
    @49
    c2o
    @51
    c1o
    @49
    wcel
    1onn
    c1o
    com
    sucidg
    ax-mp
    df-2o
    eleqtrri
    c2o
    cN
    c1o
    ssel
    mpi
    cN
    c1o
    ne0i
    syl
    adantl
    @0
    @53
    @1
    cN
    nnlim
    adantr
    cN
    onsucuni3
    syl3anc
    @2
    @26
    @15
    wceq
    #
    @27
    @23
    wceq
    @2
    @30
    @51
    @55
    @48
    1onn
    @14
    c1o
    nnacom
    sylancl
    @26
    @15
    suceq
    syl
    3eqtr3d
    @2
    @6
    com
    wcel
    #
    @15
    com
    wcel
    #
    @24
    @25
    wb
    @0
    @56
    @1
    @0
    cN
    com
    wss
    #
    cN
    cfn
    wcel
    @56
    com
    word
    @0
    @58
    ordom
    com
    cN
    ordelss
    mpan
    cN
    nnfi
    cN
    nnunifi
    syl2anc
    adantr
    @2
    @51
    @30
    @57
    1onn
    @48
    c1o
    @14
    nnacl
    sylancr
    @6
    @15
    peano4
    syl2anc
    mpbid
    fveq2d
    adantr
    @5
    @30
    c2o
    @19
    cfv
    #
    c1o
    @9
    cfv
    #
    wceq
    #
    @20
    @16
    wceq
    #
    @2
    @30
    @4
    @48
    adantr
    @5
    c1o
    @19
    cfv
    #
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    @59
    @60
    @5
    @63
    @8
    cF
    @5
    @8
    @18
    cF
    cfv
    #
    @63
    vx
    cU
    vn
    cF
    cN
    @3
    finxpreclem4.1
    finxpreclem3
    @63
    c0
    csuc
    #
    @19
    cfv
    #
    c0
    @19
    cfv
    #
    cF
    cfv
    #
    @66
    c1o
    @67
    @19
    df-1o
    fveq2i
    c0
    con0
    wcel
    #
    @68
    @70
    wceq
    0elon
    @18
    c0
    cF
    rdgsuc
    ax-mp
    @69
    @18
    cF
    @18
    cF
    cN
    @3
    opex
    rdg0
    fveq2i
    3eqtri
    syl6reqr
    fveq2d
    @59
    c2o
    cuni
    #
    @19
    cfv
    #
    cF
    cfv
    #
    @64
    @38
    c2o
    c0
    wne
    c2o
    wlim
    wn
    #
    @59
    @74
    wceq
    2on
    2on0
    @29
    @75
    2onn
    c2o
    nnlim
    ax-mp
    c2o
    cF
    @18
    rdgsucuni
    mp3an
    @63
    @73
    cF
    c1o
    @72
    @19
    1oequni2o
    fveq2i
    fveq2i
    eqtr4i
    @60
    @67
    @9
    cfv
    #
    c0
    @9
    cfv
    #
    cF
    cfv
    #
    @65
    c1o
    @67
    @9
    df-1o
    fveq2i
    @71
    @76
    @78
    wceq
    0elon
    @8
    c0
    cF
    rdgsuc
    ax-mp
    @77
    @8
    cF
    @8
    cF
    @6
    @7
    opex
    rdg0
    fveq2i
    3eqtri
    3eqtr4g
    @38
    c1o
    con0
    wcel
    @30
    @61
    @62
    wi
    2on
    1on
    @18
    @8
    cF
    c1o
    c2o
    @14
    rdgeqoa
    mp3an12
    sylc
    @2
    @20
    @21
    wceq
    @4
    @2
    @17
    cN
    @19
    @45
    fveq2d
    adantr
    3eqtr2rd
end
