include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "cv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "ctop.mm"
include "wss.mm"
include "cvv.mm"
include "wceq.mm"
include "cnfldtop.mm"
include "cneg.mm"
include "cicc.mm"
include "cxp.mm"
include "cima.mm"
include "ccnv.mm"
include "cc.mm"
include "wf1o.mm"
include "wfn.mm"
include "wb.mm"
include "cnref1o.mm"
include "f1ofn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "1st2nd2.mm"
include "ad2antrl.mm"
include "xp1st.mm"
include "recnd.mm"
include "abscld.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "cldss.mm"
include "adantr.mm"
include "simprr.mm"
include "sseldd.mm"
include "simplrl.mm"
include "cre.mm"
include "cim.mm"
include "simprl.mm"
include "f1ocnvfv1.mm"
include "sylancr.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "cnrecnv.mm"
include "opex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "absrele.mm"
include "eqbrtrd.mm"
include "simplrr.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "letrd.mm"
include "absled.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"
include "w3a.mm"
include "renegcl.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "xp2nd.mm"
include "op2nd.mm"
include "absimle.mm"
include "opelxpd.mm"
include "eqeltrd.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "wfun.mm"
include "crn.mm"
include "wi.mm"
include "f1ofun.mm"
include "ax-mp.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl6sseqr.mm"
include "funimass1.mm"
include "mpd.mm"
include "cioo.mm"
include "ctg.mm"
include "ctx.mm"
include "chmeo.mm"
include "eqid.mm"
include "cnrehmeo.mm"
include "imaexg.mm"
include "eqeltri.mm"
include "a1i.mm"
include "restabs.mm"
include "mp3an2i.mm"
include "syl6eqr.mm"
include "oveq2i.mm"
include "ccn.mm"
include "ishmeo.mm"
include "mpbi.mm"
include "simpli.mm"
include "iccssre.mm"
include "mpancom.mm"
include "rerest.mm"
include "oveq12d.mm"
include "retop.mm"
include "ovex.mm"
include "txrest.mm"
include "mp4an.mm"
include "icccmp.mm"
include "txcmp.mm"
include "eqeltrrd.mm"
include "imacmp.mm"
include "syl5eqel.mm"
include "imassrn.mm"
include "eqsstri.mm"
include "wf.mm"
include "f1of.mm"
include "frn.mm"
include "sstri.mm"
include "simpl.mm"
include "restcldi.mm"
include "cmpcld.mm"

theorem cnheiborlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cT: class T
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  assume cnheibor.2: |- J = ( TopOpen ` CCfld )
  assume cnheibor.3: |- T = ( J |`t X )
  assume cnheibor.4: |- F = ( x e. RR , y e. RR |-> ( x + ( _i x. y ) ) )
  assume cnheibor.5: |- Y = ( F " ( ( -u R [,] R ) X. ( -u R [,] R ) ) )

  disjoint F z
  disjoint R z
  disjoint x y
  disjoint x z
  disjoint T x
  disjoint y z
  disjoint T y
  disjoint T z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint u z
  disjoint F u
  disjoint R u
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint T f
  disjoint r s
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint T r
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint T s
  disjoint u x
  disjoint u y
  disjoint T u
  disjoint J r
  disjoint J u
  disjoint X f
  disjoint X r
  disjoint X s
  disjoint X u
  assert |- ( ( X e. ( Clsd ` J ) /\ ( R e. RR /\ A. z e. X ( abs ` z ) <_ R ) ) -> T e. Comp )

  proof
    cX
    cJ
    ccld
    cfv
    wcel
    #
    cR
    cr
    wcel
    #
    vz
    cv
    #
    cabs
    cfv
    #
    cR
    cle
    wbr
    #
    vz
    cX
    wral
    #
    wa
    #
    wa
    #
    cJ
    cY
    crest
    co
    #
    cX
    crest
    co
    #
    cT
    ccmp
    @7
    @9
    cJ
    cX
    crest
    co
    #
    cT
    cJ
    ctop
    wcel
    @7
    cX
    cY
    wss
    #
    cY
    cvv
    wcel
    #
    @9
    @10
    wceq
    cJ
    cnheibor.2
    cnfldtop
    @7
    cX
    cF
    cR
    cneg
    #
    cR
    cicc
    co
    #
    @14
    cxp
    #
    cima
    #
    cY
    @7
    cF
    ccnv
    #
    cX
    cima
    #
    @15
    wss
    #
    cX
    @16
    wss
    #
    @7
    vu
    @18
    @15
    vu
    cv
    #
    @18
    wcel
    #
    @21
    cr
    cr
    cxp
    #
    wcel
    #
    @21
    cF
    cfv
    #
    cX
    wcel
    #
    wa
    #
    @7
    @21
    @15
    wcel
    #
    @23
    cc
    cF
    wf1o
    #
    cF
    @23
    wfn
    @22
    @27
    wb
    vx
    vy
    cF
    cnheibor.4
    cnref1o
    #
    @23
    cc
    cF
    f1ofn
    @23
    @21
    cX
    cF
    elpreima
    mp2b
    @7
    @27
    @28
    @7
    @27
    wa
    #
    @21
    @21
    c1st
    cfv
    #
    @21
    c2nd
    cfv
    #
    cop
    #
    @15
    @24
    @21
    @34
    wceq
    @7
    @26
    @21
    cr
    cr
    1st2nd2
    ad2antrl
    @31
    @32
    @33
    @14
    @14
    @31
    @32
    @14
    wcel
    #
    @32
    cr
    wcel
    #
    @13
    @32
    cle
    wbr
    #
    @32
    cR
    cle
    wbr
    #
    @24
    @36
    @7
    @26
    @21
    cr
    cr
    xp1st
    ad2antrl
    #
    @31
    @37
    @38
    @31
    @32
    cabs
    cfv
    #
    cR
    cle
    wbr
    @37
    @38
    wa
    @31
    @40
    @25
    cabs
    cfv
    #
    cR
    @31
    @32
    @31
    @32
    @39
    recnd
    abscld
    @31
    @25
    @31
    cX
    cc
    @25
    @7
    cX
    cc
    wss
    #
    @27
    @0
    @42
    @6
    cX
    cJ
    cc
    cc
    cJ
    cJ
    cnheibor.2
    cnfldtopon
    toponunii
    #
    cldss
    adantr
    #
    adantr
    @7
    @24
    @26
    simprr
    #
    sseldd
    #
    abscld
    #
    @0
    @1
    @5
    @27
    simplrl
    #
    @31
    @40
    @25
    cre
    cfv
    #
    cabs
    cfv
    #
    @41
    cle
    @31
    @32
    @49
    cabs
    @31
    @32
    @49
    @25
    cim
    cfv
    #
    cop
    #
    c1st
    cfv
    @49
    @31
    @21
    @52
    c1st
    @31
    @25
    @17
    cfv
    #
    @21
    @52
    @31
    @29
    @24
    @53
    @21
    wceq
    @30
    @7
    @24
    @26
    simprl
    @23
    cc
    @21
    cF
    f1ocnvfv1
    sylancr
    @31
    @25
    cc
    wcel
    #
    @53
    @52
    wceq
    @46
    vz
    @25
    @2
    cre
    cfv
    #
    @2
    cim
    cfv
    #
    cop
    @52
    cc
    @17
    @2
    @25
    wceq
    #
    @55
    @49
    @56
    @51
    @2
    @25
    cre
    fveq2
    @2
    @25
    cim
    fveq2
    opeq12d
    vx
    vy
    vz
    cF
    cnheibor.4
    cnrecnv
    @49
    @51
    opex
    fvmpt
    syl
    eqtr3d
    #
    fveq2d
    @49
    @51
    @25
    cre
    fvex
    #
    @25
    cim
    fvex
    #
    op1st
    syl6eq
    fveq2d
    @31
    @54
    @50
    @41
    cle
    wbr
    @46
    @25
    absrele
    syl
    eqbrtrd
    @31
    @26
    @5
    @41
    cR
    cle
    wbr
    #
    @45
    @0
    @1
    @5
    @27
    simplrr
    @4
    @61
    vz
    @25
    cX
    @57
    @3
    @41
    cR
    cle
    @2
    @25
    cabs
    fveq2
    breq1d
    rspcv
    sylc
    #
    letrd
    @31
    @32
    cR
    @39
    @48
    absled
    mpbid
    #
    simpld
    @31
    @37
    @38
    @63
    simprd
    @31
    @13
    cr
    wcel
    #
    @1
    @35
    @36
    @37
    @38
    w3a
    wb
    @31
    @1
    @64
    @48
    cR
    renegcl
    #
    syl
    #
    @48
    @13
    cR
    @32
    elicc2
    syl2anc
    mpbir3and
    @31
    @33
    @14
    wcel
    #
    @33
    cr
    wcel
    #
    @13
    @33
    cle
    wbr
    #
    @33
    cR
    cle
    wbr
    #
    @24
    @68
    @7
    @26
    @21
    cr
    cr
    xp2nd
    ad2antrl
    #
    @31
    @69
    @70
    @31
    @33
    cabs
    cfv
    #
    cR
    cle
    wbr
    @69
    @70
    wa
    @31
    @72
    @41
    cR
    @31
    @33
    @31
    @33
    @71
    recnd
    abscld
    @47
    @48
    @31
    @72
    @51
    cabs
    cfv
    #
    @41
    cle
    @31
    @33
    @51
    cabs
    @31
    @33
    @52
    c2nd
    cfv
    @51
    @31
    @21
    @52
    c2nd
    @58
    fveq2d
    @49
    @51
    @59
    @60
    op2nd
    syl6eq
    fveq2d
    @31
    @54
    @73
    @41
    cle
    wbr
    @46
    @25
    absimle
    syl
    eqbrtrd
    @62
    letrd
    @31
    @33
    cR
    @71
    @48
    absled
    mpbid
    #
    simpld
    @31
    @69
    @70
    @74
    simprd
    @31
    @64
    @1
    @67
    @68
    @69
    @70
    w3a
    wb
    @66
    @48
    @13
    cR
    @33
    elicc2
    syl2anc
    mpbir3and
    opelxpd
    eqeltrd
    ex
    syl5bi
    ssrdv
    @7
    cF
    wfun
    #
    cX
    cF
    crn
    #
    wss
    @19
    @20
    wi
    @29
    @75
    @30
    @23
    cc
    cF
    f1ofun
    ax-mp
    @7
    cX
    cc
    @76
    @44
    @29
    @23
    cc
    cF
    wfo
    @76
    cc
    wceq
    @30
    @23
    cc
    cF
    f1ofo
    @23
    cc
    cF
    forn
    mp2b
    syl6sseqr
    cX
    @15
    cF
    funimass1
    sylancr
    mpd
    cnheibor.5
    syl6sseqr
    #
    @12
    @7
    cY
    @16
    cvv
    cnheibor.5
    cF
    cioo
    crn
    ctg
    cfv
    #
    @78
    ctx
    co
    #
    cJ
    chmeo
    co
    #
    wcel
    #
    @16
    cvv
    wcel
    vx
    vy
    cF
    @78
    cJ
    cnheibor.4
    @78
    eqid
    #
    cnheibor.2
    cnrehmeo
    #
    cF
    @15
    @80
    imaexg
    ax-mp
    eqeltri
    a1i
    cX
    cY
    cJ
    ctop
    cvv
    restabs
    mp3an2i
    cnheibor.3
    syl6eqr
    @7
    @8
    ccmp
    wcel
    #
    cX
    @8
    ccld
    cfv
    wcel
    #
    @9
    ccmp
    wcel
    @1
    @84
    @0
    @5
    @1
    @8
    cJ
    @16
    crest
    co
    #
    ccmp
    cY
    @16
    cJ
    crest
    cnheibor.5
    oveq2i
    @1
    cF
    @79
    cJ
    ccn
    co
    wcel
    #
    @79
    @15
    crest
    co
    #
    ccmp
    wcel
    @86
    ccmp
    wcel
    @87
    @17
    cJ
    @79
    ccn
    co
    wcel
    #
    @81
    @87
    @89
    wa
    @83
    cF
    @79
    cJ
    ishmeo
    mpbi
    simpli
    @1
    cJ
    @14
    crest
    co
    #
    @90
    ctx
    co
    #
    @88
    ccmp
    @1
    @91
    @78
    @14
    crest
    co
    #
    @92
    ctx
    co
    #
    @88
    @1
    @90
    @92
    @90
    @92
    ctx
    @1
    @14
    cr
    wss
    #
    @90
    @92
    wceq
    @64
    @1
    @94
    @65
    @13
    cR
    iccssre
    mpancom
    @14
    @78
    cJ
    cnheibor.2
    @82
    rerest
    syl
    #
    @95
    oveq12d
    @78
    ctop
    wcel
    #
    @96
    @14
    cvv
    wcel
    #
    @97
    @88
    @93
    wceq
    retop
    retop
    @13
    cR
    cicc
    ovex
    #
    @98
    @14
    @14
    @78
    @78
    ctop
    ctop
    cvv
    cvv
    txrest
    mp4an
    syl6eqr
    @1
    @90
    ccmp
    wcel
    #
    @99
    @91
    ccmp
    wcel
    @1
    @90
    @92
    ccmp
    @95
    @64
    @1
    @92
    ccmp
    wcel
    @65
    @13
    cR
    @92
    @78
    @82
    @92
    eqid
    icccmp
    mpancom
    eqeltrd
    #
    @100
    @90
    @90
    txcmp
    syl2anc
    eqeltrrd
    @15
    cF
    @79
    cJ
    imacmp
    sylancr
    syl5eqel
    ad2antrl
    cY
    cc
    wss
    @7
    @0
    @11
    @85
    cY
    @76
    cc
    cY
    @16
    @76
    cnheibor.5
    cF
    @15
    imassrn
    eqsstri
    @29
    @23
    cc
    cF
    wf
    @76
    cc
    wss
    @30
    @23
    cc
    cF
    f1of
    @23
    cc
    cF
    frn
    mp2b
    sstri
    @0
    @6
    simpl
    @77
    cY
    cX
    cJ
    cc
    @43
    restcldi
    mp3an2i
    cX
    @8
    cmpcld
    syl2anc
    eqeltrrd
end
