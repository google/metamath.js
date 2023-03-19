include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "csuc.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "w3a.mm"
include "cfv.mm"
include "cab.mm"
include "cio.mm"
include "cmpt.mm"
include "crio.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cif.mm"
include "iffalse.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "3ad2ant1.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "breq2.mm"
include "notbid.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "3impb.mm"
include "weq.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "3ad2ant3.mm"
include "wb.mm"
include "simp32.mm"
include "eleq1.mm"
include "suceq.mm"
include "reseq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "rexbidv.mm"
include "elabg.mm"
include "syl.mm"
include "mpbird.mm"
include "fveq2.mm"
include "3anbi123d.mm"
include "iotabidv.mm"
include "eqid.mm"
include "iotaex.mm"
include "fvmpt.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqidd.mm"
include "fveq1.mm"
include "syl13anc.mm"
include "weu.mm"
include "fvex.mm"
include "wex.mm"
include "wmo.mm"
include "eqeq2.mm"
include "3anbi3d.mm"
include "spcev.mm"
include "mp3an3.mm"
include "reximi.mm"
include "rexcom4.mm"
include "sylib.mm"
include "noprefixmo.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "eu5.mm"
include "sylanbrc.mm"
include "iota2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "3eqtrd.mm"

theorem nosupfv
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  let cG: class G
  let vp: setvar p
  assume nosupfv.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A g
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint G g
  disjoint g u
  disjoint G u
  disjoint g v
  disjoint G v
  disjoint g x
  disjoint G x
  disjoint g y
  disjoint G y
  disjoint U u
  disjoint u v
  disjoint U v
  disjoint u x
  disjoint U x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint A p
  disjoint G p
  disjoint p u
  disjoint p v
  disjoint U p
  assert |- ( ( -. E. x e. A A. y e. A -. x <s y /\ ( A C_ No /\ A e. _V ) /\ ( U e. A /\ G e. dom U /\ A. v e. A ( -. v <s U -> ( U |` suc G ) = ( v |` suc G ) ) ) ) -> ( S ` G ) = ( U ` G ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cslt
    wbr
    wn
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    wn
    #
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cU
    cA
    wcel
    #
    cG
    cU
    cdm
    #
    wcel
    #
    vv
    cv
    #
    cU
    cslt
    wbr
    #
    wn
    #
    cU
    cG
    csuc
    #
    cres
    #
    @11
    @14
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    w3a
    #
    w3a
    #
    cG
    cS
    cfv
    #
    cG
    vg
    @1
    vu
    cv
    #
    cdm
    #
    wcel
    #
    @11
    @23
    cslt
    wbr
    #
    wn
    #
    @23
    @1
    csuc
    #
    cres
    #
    @11
    @28
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vu
    cA
    wrex
    #
    vy
    cab
    #
    vg
    cv
    #
    @24
    wcel
    #
    @27
    @23
    @37
    csuc
    #
    cres
    #
    @11
    @39
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    @37
    @23
    cfv
    #
    @0
    wceq
    #
    w3a
    #
    vu
    cA
    wrex
    #
    vx
    cio
    #
    cmpt
    #
    cfv
    #
    cG
    @24
    wcel
    #
    @27
    @23
    @14
    cres
    #
    @16
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    cG
    @23
    cfv
    #
    @0
    wceq
    #
    w3a
    #
    vu
    cA
    wrex
    #
    vx
    cio
    #
    cG
    cU
    cfv
    #
    @4
    @7
    @22
    @51
    wceq
    @20
    @4
    cG
    cS
    @50
    @4
    cS
    @3
    @2
    vx
    cA
    crio
    #
    @63
    cdm
    c2o
    cop
    csn
    cun
    #
    @50
    cif
    @50
    nosupfv.1
    @3
    @64
    @50
    iffalse
    syl5eq
    fveq1d
    3ad2ant1
    @21
    cG
    @36
    wcel
    #
    @51
    @61
    wceq
    @21
    @65
    @52
    @56
    wa
    #
    vu
    cA
    wrex
    #
    @20
    @4
    @67
    @7
    @20
    cG
    vp
    cv
    #
    cdm
    #
    wcel
    #
    @11
    @68
    cslt
    wbr
    #
    wn
    #
    @68
    @14
    cres
    #
    @16
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    #
    @67
    @8
    @10
    @19
    @78
    @77
    @10
    @19
    wa
    vp
    cU
    cA
    @68
    cU
    wceq
    #
    @70
    @10
    @76
    @19
    @79
    @69
    @9
    cG
    @68
    cU
    dmeq
    eleq2d
    @79
    @75
    @18
    vv
    cA
    @79
    @72
    @13
    @74
    @17
    @79
    @71
    @12
    @68
    cU
    @11
    cslt
    breq2
    notbid
    @79
    @73
    @15
    @16
    @68
    cU
    @14
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    anbi12d
    rspcev
    3impb
    @66
    @77
    vu
    vp
    cA
    vu
    vp
    weq
    #
    @52
    @70
    @56
    @76
    @80
    @24
    @69
    cG
    @23
    @68
    dmeq
    eleq2d
    @80
    @55
    @75
    vv
    cA
    @80
    @27
    @72
    @54
    @74
    @80
    @26
    @71
    @23
    @68
    @11
    cslt
    breq2
    notbid
    @80
    @53
    @73
    @16
    @23
    @68
    @14
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    anbi12d
    cbvrexv
    sylibr
    #
    3ad2ant3
    @21
    @10
    @65
    @67
    wb
    @4
    @7
    @8
    @10
    @19
    simp32
    @35
    @67
    vy
    cG
    @9
    @1
    cG
    wceq
    #
    @34
    @66
    vu
    cA
    @82
    @25
    @52
    @33
    @56
    @1
    cG
    @24
    eleq1
    @82
    @32
    @55
    vv
    cA
    @82
    @31
    @54
    @27
    @82
    @29
    @53
    @30
    @16
    @82
    @28
    @14
    @23
    @1
    cG
    suceq
    #
    reseq2d
    @82
    @28
    @14
    @11
    @83
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    elabg
    syl
    mpbird
    vg
    cG
    @49
    @61
    @36
    @50
    @37
    cG
    wceq
    #
    @48
    @60
    vx
    @84
    @47
    @59
    vu
    cA
    @84
    @38
    @52
    @44
    @56
    @46
    @58
    @37
    cG
    @24
    eleq1
    @84
    @43
    @55
    vv
    cA
    @84
    @42
    @54
    @27
    @84
    @40
    @53
    @41
    @16
    @84
    @39
    @14
    @23
    @37
    cG
    suceq
    #
    reseq2d
    @84
    @39
    @14
    @11
    @85
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    @84
    @45
    @57
    @0
    @37
    cG
    @23
    fveq2
    eqeq1d
    3anbi123d
    rexbidv
    iotabidv
    @50
    eqid
    @60
    vx
    iotaex
    fvmpt
    syl
    @21
    @52
    @56
    @57
    @62
    wceq
    #
    w3a
    #
    vu
    cA
    wrex
    #
    @61
    @62
    wceq
    #
    @20
    @4
    @88
    @7
    @20
    @8
    @10
    @19
    @62
    @62
    wceq
    #
    @88
    @8
    @10
    @19
    simp1
    @8
    @10
    @19
    simp2
    @8
    @10
    @19
    simp3
    @20
    @62
    eqidd
    @87
    @10
    @19
    @90
    w3a
    vu
    cU
    cA
    @23
    cU
    wceq
    #
    @52
    @10
    @56
    @19
    @86
    @90
    @91
    @24
    @9
    cG
    @23
    cU
    dmeq
    eleq2d
    @91
    @55
    @18
    vv
    cA
    @91
    @27
    @13
    @54
    @17
    @91
    @26
    @12
    @23
    cU
    @11
    cslt
    breq2
    notbid
    @91
    @53
    @15
    @16
    @23
    cU
    @14
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    @91
    @57
    @62
    @62
    cG
    @23
    cU
    fveq1
    eqeq1d
    3anbi123d
    rspcev
    syl13anc
    3ad2ant3
    @21
    @62
    cvv
    wcel
    @60
    vx
    weu
    #
    @88
    @89
    wb
    cG
    cU
    fvex
    @21
    @60
    vx
    wex
    #
    @60
    vx
    wmo
    #
    @92
    @20
    @4
    @93
    @7
    @20
    @67
    @93
    @81
    @67
    @59
    vx
    wex
    #
    vu
    cA
    wrex
    @93
    @66
    @95
    vu
    cA
    @52
    @56
    @57
    @57
    wceq
    #
    @95
    @57
    eqid
    @59
    @52
    @56
    @96
    w3a
    vx
    @57
    cG
    @23
    fvex
    @0
    @57
    wceq
    @58
    @96
    @52
    @56
    @0
    @57
    @57
    eqeq2
    3anbi3d
    spcev
    mp3an3
    reximi
    @59
    vu
    vx
    cA
    rexcom4
    sylib
    syl
    3ad2ant3
    @7
    @4
    @94
    @20
    @5
    @94
    @6
    vx
    vv
    vu
    cA
    cG
    noprefixmo
    adantr
    3ad2ant2
    @60
    vx
    eu5
    sylanbrc
    @60
    @88
    vx
    @62
    cvv
    @0
    @62
    wceq
    #
    @59
    @87
    vu
    cA
    @97
    @58
    @86
    @52
    @56
    @0
    @62
    @57
    eqeq2
    3anbi3d
    rexbidv
    iota2
    sylancr
    mpbid
    3eqtrd
end
