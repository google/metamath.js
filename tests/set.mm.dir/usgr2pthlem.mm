include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1.mm"
include "cfz.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "wral.mm"
include "cusgr.mm"
include "wcel.mm"
include "c2.mm"
include "wa.mm"
include "w3a.mm"
include "cdif.mm"
include "wrex.mm"
include "csn.mm"
include "wi.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "0nn0.mm"
include "2nn0.mm"
include "0le2.mm"
include "elfz2nn0.mm"
include "mpbir3an.mm"
include "ffvelrn.mm"
include "mpan2.mm"
include "adantl.mm"
include "1nn0.mm"
include "1le2.mm"
include "wne.mm"
include "wn.mm"
include "cvv.mm"
include "simpr.mm"
include "fvex.mm"
include "jctir.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "biimpi.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "usgrnloopv.mm"
include "sylc.mm"
include "elsn.mm"
include "necon3bbii.mm"
include "sylibr.mm"
include "eldifd.mm"
include "wb.mm"
include "sneq.mm"
include "difeq2d.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "2re.mm"
include "leidi.mm"
include "crn.mm"
include "usgrf1.mm"
include "simpl.mm"
include "ad2antrr.mm"
include "jca.mm"
include "cn.mm"
include "2nn.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "clt.mm"
include "1lt2.mm"
include "elfzo0.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "0ne1.mm"
include "3jca.mm"
include "2f1fvneq.mm"
include "necom.mm"
include "3pm3.2i.mm"
include "fvexd.mm"
include "jca31.mm"
include "imp.mm"
include "syl.mm"
include "pr1nebg.mm"
include "sylancr.mm"
include "syl5bb.mm"
include "nelprd.mm"
include "preq12.mm"
include "adantll.mm"
include "eqcom.mm"
include "3anbi123i.mm"
include "ad4ant123.mm"
include "preq12d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "biimpa.mm"
include "exp41.mm"
include "imp31.mm"
include "rspcimedv.mm"
include "com15.mm"
include "pm2.43i.mm"
include "com12.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "fzo0to2pr.mm"
include "raleqi.mm"
include "2wlklem.mm"
include "bitri.mm"
include "syl6bb.mm"
include "feq2d.mm"
include "f1eq2.mm"
include "imbi1d.mm"
include "imbi12d.mm"
include "3imtr4d.mm"
include "com14.mm"
include "com23.mm"
include "3imp.mm"

theorem usgr2pthlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  assume usgr2pthlem.v: |- V = ( Vtx ` G )
  assume usgr2pthlem.i: |- I = ( iEdg ` G )

  disjoint F i
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I i
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P i
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ( F : ( 0 ..^ ( # ` F ) ) -1-1-> dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. i e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` i ) ) = { ( P ` i ) , ( P ` ( i + 1 ) ) } ) -> ( ( G e. USGraph /\ ( # ` F ) = 2 ) -> E. x e. V E. y e. ( V \ { x } ) E. z e. ( V \ { x , y } ) ( ( ( P ` 0 ) = x /\ ( P ` 1 ) = y /\ ( P ` 2 ) = z ) /\ ( ( I ` ( F ` 0 ) ) = { x , y } /\ ( I ` ( F ` 1 ) ) = { y , z } ) ) ) )

  proof
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cdm
    #
    cF
    wf1
    #
    cc0
    @0
    cfz
    co
    #
    cV
    cP
    wf
    #
    vi
    cv
    #
    cF
    cfv
    cI
    cfv
    @6
    cP
    cfv
    @6
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    #
    vi
    @1
    wral
    #
    cG
    cusgr
    wcel
    #
    @0
    c2
    wceq
    #
    wa
    #
    cc0
    cP
    cfv
    #
    vx
    cv
    #
    wceq
    #
    c1
    cP
    cfv
    #
    vy
    cv
    #
    wceq
    #
    c2
    cP
    cfv
    #
    vz
    cv
    #
    wceq
    #
    w3a
    #
    cc0
    cF
    cfv
    #
    cI
    cfv
    #
    @13
    @16
    cpr
    #
    wceq
    #
    c1
    cF
    cfv
    #
    cI
    cfv
    #
    @16
    @19
    cpr
    #
    wceq
    #
    wa
    #
    wa
    #
    vz
    cV
    @24
    cdif
    #
    wrex
    #
    vy
    cV
    @13
    csn
    #
    cdif
    #
    wrex
    #
    vx
    cV
    wrex
    #
    wi
    #
    @3
    @8
    @5
    @38
    @11
    @8
    @5
    @3
    @37
    @11
    @23
    @12
    @15
    cpr
    #
    wceq
    #
    @27
    @15
    @18
    cpr
    #
    wceq
    #
    wa
    #
    cc0
    c2
    cfz
    co
    #
    cV
    cP
    wf
    #
    cc0
    c2
    cfzo
    co
    #
    @2
    cF
    wf1
    #
    @37
    wi
    #
    wi
    #
    @8
    @5
    @3
    @37
    wi
    #
    wi
    @9
    @43
    @49
    wi
    @10
    @43
    @9
    @49
    @43
    @9
    @49
    wi
    @47
    @43
    @9
    @45
    @43
    @37
    @47
    @43
    @9
    @45
    @43
    @37
    wi
    @47
    @43
    wa
    #
    @9
    wa
    #
    @45
    wa
    #
    @36
    @43
    vx
    @12
    cV
    @45
    @12
    cV
    wcel
    #
    @52
    @45
    cc0
    @44
    wcel
    #
    @54
    @55
    cc0
    cn0
    wcel
    c2
    cn0
    wcel
    #
    cc0
    c2
    cle
    wbr
    0nn0
    2nn0
    0le2
    cc0
    c2
    elfz2nn0
    mpbir3an
    @44
    cV
    cc0
    cP
    ffvelrn
    mpan2
    adantl
    @53
    @13
    @12
    wceq
    #
    wa
    #
    @33
    @43
    vy
    @15
    @35
    @58
    @15
    @35
    wcel
    #
    @15
    cV
    @12
    csn
    #
    cdif
    #
    wcel
    #
    @53
    @62
    @57
    @53
    @15
    cV
    @60
    @45
    @15
    cV
    wcel
    #
    @52
    @45
    c1
    @44
    wcel
    #
    @63
    @64
    c1
    cn0
    wcel
    #
    @56
    c1
    c2
    cle
    wbr
    1nn0
    2nn0
    1le2
    c1
    c2
    elfz2nn0
    mpbir3an
    @44
    cV
    c1
    cP
    ffvelrn
    mpan2
    adantl
    @53
    @15
    @12
    wne
    #
    @15
    @60
    wcel
    #
    wn
    @52
    @66
    @45
    @52
    @9
    @15
    cvv
    wcel
    #
    wa
    @23
    @15
    @12
    cpr
    #
    wceq
    #
    @66
    @52
    @9
    @68
    @51
    @9
    simpr
    #
    c1
    cP
    fvex
    #
    jctir
    @43
    @70
    @47
    @9
    @40
    @70
    @42
    @40
    @70
    @39
    @69
    @23
    @12
    @15
    prcom
    eqeq2i
    biimpi
    adantr
    ad2antlr
    cI
    cG
    @15
    @12
    cvv
    @22
    usgr2pthlem.i
    usgrnloopv
    sylc
    adantr
    @67
    @15
    @12
    @15
    @12
    @72
    elsn
    necon3bbii
    sylibr
    eldifd
    adantr
    @57
    @59
    @62
    wb
    @53
    @57
    @35
    @61
    @15
    @57
    @34
    @60
    cV
    @13
    @12
    sneq
    difeq2d
    eleq2d
    adantl
    mpbird
    @58
    @16
    @15
    wceq
    #
    wa
    #
    @31
    @43
    vz
    @18
    @32
    @74
    @18
    @32
    wcel
    #
    @18
    cV
    @39
    cdif
    #
    wcel
    #
    @53
    @77
    @57
    @73
    @53
    @18
    cV
    @39
    @45
    @18
    cV
    wcel
    #
    @52
    @45
    c2
    @44
    wcel
    #
    @78
    @79
    @56
    @56
    c2
    c2
    cle
    wbr
    2nn0
    2nn0
    c2
    2re
    leidi
    c2
    c2
    elfz2nn0
    mpbir3an
    @44
    cV
    c2
    cP
    ffvelrn
    mpan2
    adantl
    @53
    @18
    @12
    @15
    @53
    @18
    @12
    wne
    #
    @39
    @41
    wne
    #
    @53
    @2
    cI
    crn
    #
    cI
    wf1
    #
    @47
    wa
    #
    cc0
    @46
    wcel
    #
    c1
    @46
    wcel
    #
    wa
    #
    cc0
    c1
    wne
    #
    w3a
    @43
    @81
    @53
    @84
    @87
    @88
    @53
    @83
    @47
    @9
    @83
    @51
    @45
    cI
    cG
    usgr2pthlem.i
    usgrf1
    ad2antlr
    @51
    @47
    @9
    @45
    @47
    @43
    simpl
    ad2antrr
    jca
    @87
    @53
    @85
    @86
    @85
    c2
    cn
    wcel
    #
    2nn
    c2
    lbfzo0
    mpbir
    @86
    @65
    @89
    c1
    c2
    clt
    wbr
    1nn0
    2nn
    1lt2
    c1
    c2
    elfzo0
    mpbir3an
    pm3.2i
    a1i
    @88
    @53
    0ne1
    a1i
    3jca
    @51
    @43
    @9
    @45
    @47
    @43
    simpr
    ad2antrr
    cc0
    c1
    @46
    @2
    @82
    cI
    cF
    @39
    @41
    2f1fvneq
    sylc
    @80
    @12
    @18
    wne
    #
    @53
    @81
    @18
    @12
    necom
    @53
    @12
    cvv
    wcel
    #
    @68
    @18
    cvv
    wcel
    #
    w3a
    @12
    @15
    wne
    #
    @90
    @81
    wb
    @91
    @68
    @92
    cc0
    cP
    fvex
    @72
    c2
    cP
    fvex
    3pm3.2i
    @53
    @9
    @91
    wa
    #
    @40
    wa
    #
    @93
    @52
    @95
    @45
    @52
    @9
    @91
    @40
    @71
    @52
    cc0
    cP
    fvexd
    @43
    @40
    @47
    @9
    @40
    @42
    simpl
    ad2antlr
    jca31
    adantr
    @94
    @40
    @93
    cI
    cG
    @12
    @15
    cvv
    @22
    usgr2pthlem.i
    usgrnloopv
    imp
    syl
    @12
    @15
    @18
    cvv
    cvv
    cvv
    pr1nebg
    sylancr
    syl5bb
    mpbird
    @53
    @9
    @92
    wa
    #
    @27
    @18
    @15
    cpr
    #
    wceq
    #
    wa
    #
    @18
    @15
    wne
    #
    @52
    @99
    @45
    @52
    @9
    @92
    @98
    @71
    @52
    c2
    cP
    fvexd
    @43
    @98
    @47
    @9
    @42
    @98
    @40
    @42
    @98
    @41
    @97
    @27
    @15
    @18
    prcom
    eqeq2i
    biimpi
    adantl
    ad2antlr
    jca31
    adantr
    @96
    @98
    @100
    cI
    cG
    @18
    @15
    cvv
    @26
    usgr2pthlem.i
    usgrnloopv
    imp
    syl
    nelprd
    eldifd
    ad2antrr
    @57
    @73
    @75
    @77
    wb
    @53
    @57
    @73
    wa
    #
    @32
    @76
    @18
    @101
    @24
    @39
    cV
    @13
    @16
    @12
    @15
    preq12
    difeq2d
    eleq2d
    adantll
    mpbird
    @58
    @73
    @19
    @18
    wceq
    #
    @43
    @31
    wi
    #
    @57
    @73
    @102
    @103
    wi
    wi
    @53
    @57
    @73
    @102
    @43
    @31
    @101
    @102
    wa
    #
    @43
    wa
    @21
    @30
    @57
    @73
    @102
    @21
    @43
    @57
    @73
    @102
    w3a
    @21
    @57
    @14
    @73
    @17
    @102
    @20
    @13
    @12
    eqcom
    #
    @16
    @15
    eqcom
    #
    @19
    @18
    eqcom
    #
    3anbi123i
    biimpi
    ad4ant123
    @104
    @43
    @30
    @104
    @40
    @25
    @42
    @29
    @104
    @39
    @24
    @23
    @104
    @12
    @13
    @15
    @16
    @57
    @14
    @73
    @102
    @57
    @14
    @105
    biimpi
    ad2antrr
    @73
    @17
    @57
    @102
    @73
    @17
    @106
    biimpi
    ad2antlr
    #
    preq12d
    eqeq2d
    @104
    @41
    @28
    @27
    @104
    @15
    @16
    @18
    @19
    @108
    @102
    @20
    @101
    @102
    @20
    @107
    biimpi
    adantl
    preq12d
    eqeq2d
    anbi12d
    biimpa
    jca
    exp41
    adantl
    imp31
    rspcimedv
    rspcimedv
    rspcimedv
    exp41
    com15
    pm2.43i
    com12
    adantr
    @10
    @8
    @43
    wb
    @9
    @10
    @8
    @7
    vi
    @46
    wral
    #
    @43
    @10
    @7
    vi
    @1
    @46
    @0
    c2
    cc0
    cfzo
    oveq2
    #
    raleqdv
    @109
    @7
    vi
    cc0
    c1
    cpr
    #
    wral
    @43
    @7
    vi
    @46
    @111
    fzo0to2pr
    raleqi
    cP
    vi
    cI
    cF
    2wlklem
    bitri
    syl6bb
    adantl
    @11
    @5
    @45
    @50
    @48
    @10
    @5
    @45
    wb
    @9
    @10
    @4
    @44
    cV
    cP
    @0
    c2
    cc0
    cfz
    oveq2
    feq2d
    adantl
    @10
    @50
    @48
    wb
    @9
    @10
    @3
    @47
    @37
    @10
    @1
    @46
    wceq
    @3
    @47
    wb
    @110
    @1
    @46
    @2
    cF
    f1eq2
    syl
    imbi1d
    adantl
    imbi12d
    3imtr4d
    com14
    com23
    3imp
end
