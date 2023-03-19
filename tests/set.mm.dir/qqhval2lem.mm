include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "wne.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "cdiv.mm"
include "cmul.mm"
include "cnumer.mm"
include "cdenom.mm"
include "zring.mm"
include "crh.mm"
include "cui.mm"
include "crg.mm"
include "drngring.mm"
include "zrhrhm.mm"
include "syl.mm"
include "ad2antrr.mm"
include "cdvds.mm"
include "wbr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "gcdcld.mm"
include "nn0zd.mm"
include "simpr3.mm"
include "gcdeq0.mm"
include "simplbda.mm"
include "ex.mm"
include "necon3d.mm"
include "imp.mm"
include "syl21anc.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "dvdsval2.mm"
include "biimpa.mm"
include "syl31anc.mm"
include "simprd.mm"
include "c0g.mm"
include "wf.mm"
include "zringbas.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "wfn.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wn.mm"
include "ffn.mm"
include "zcnd.mm"
include "divne0d.mm"
include "ovex.mm"
include "elsn.mm"
include "necon3bbii.mm"
include "sylibr.mm"
include "simplr.mm"
include "eqid.mm"
include "zrhker.mm"
include "neleqtrrd.mm"
include "elpreima.mm"
include "baibd.mm"
include "biimprd.mm"
include "con3dimp.mm"
include "fvex.mm"
include "sylib.mm"
include "wb.mm"
include "drngunit.mm"
include "mpbir2and.mm"
include "zringmulr.mm"
include "rhmdvd.mm"
include "syl132anc.mm"
include "cn.mm"
include "cneg.mm"
include "divnumden.mm"
include "sylan.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "c1.mm"
include "adantr.mm"
include "mulm1d.mm"
include "cc.mm"
include "neg1cn.mm"
include "a1i.mm"
include "mulcomd.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "divnumden2.mm"
include "syl3anc.mm"
include "1zzd.mm"
include "znegcld.mm"
include "cabs.mm"
include "neg1z.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "zringunit.mm"
include "mpbir2an.mm"
include "elrhmunit.mm"
include "3eqtr4rd.mm"
include "wo.mm"
include "simp3.mm"
include "neneqd.mm"
include "w3o.mm"
include "cr.mm"
include "simp2.mm"
include "elz.mm"
include "3orass.mm"
include "orel1.mm"
include "sylc.mm"
include "adantl.mm"
include "mpjaodan.mm"
include "divcan1d.mm"
include "3eqtr3d.mm"

theorem qqhval2lem
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cL: class L
  let cX: class X
  let cY: class Y
  assume qqhval2.0: |- B = ( Base ` R )
  assume qqhval2.1: |- ./ = ( /r ` R )
  assume qqhval2.2: |- L = ( ZRHom ` R )


  assert |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 ) /\ ( X e. ZZ /\ Y e. ZZ /\ Y =/= 0 ) ) -> ( ( L ` ( numer ` ( X / Y ) ) ) ./ ( L ` ( denom ` ( X / Y ) ) ) ) = ( ( L ` X ) ./ ( L ` Y ) ) )

  proof
    cR
    cdr
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    wa
    #
    cX
    cz
    wcel
    #
    cY
    cz
    wcel
    #
    cY
    cc0
    wne
    #
    w3a
    #
    wa
    #
    cX
    cX
    cY
    cgcd
    co
    #
    cdiv
    co
    #
    cL
    cfv
    #
    cY
    @8
    cdiv
    co
    #
    cL
    cfv
    #
    c.dv
    co
    #
    @9
    @8
    cmul
    co
    #
    cL
    cfv
    #
    @11
    @8
    cmul
    co
    #
    cL
    cfv
    #
    c.dv
    co
    #
    cX
    cY
    cdiv
    co
    #
    cnumer
    cfv
    #
    cL
    cfv
    #
    @19
    cdenom
    cfv
    #
    cL
    cfv
    #
    c.dv
    co
    #
    cX
    cL
    cfv
    #
    cY
    cL
    cfv
    #
    c.dv
    co
    @7
    cL
    zring
    cR
    crh
    co
    wcel
    #
    @9
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @12
    cR
    cui
    cfv
    #
    wcel
    #
    @8
    cL
    cfv
    #
    @31
    wcel
    #
    @13
    @18
    wceq
    @0
    @27
    @1
    @6
    @0
    cR
    crg
    wcel
    #
    @27
    cR
    drngring
    #
    cR
    cL
    qqhval2.2
    zrhrhm
    syl
    ad2antrr
    #
    @7
    @30
    @8
    cc0
    wne
    #
    @3
    @8
    cX
    cdvds
    wbr
    #
    @28
    @7
    @8
    @7
    cX
    cY
    @2
    @3
    @4
    @5
    simpr1
    #
    @2
    @3
    @4
    @5
    simpr2
    #
    gcdcld
    nn0zd
    #
    @7
    @3
    @4
    @5
    @38
    @40
    @41
    @2
    @3
    @4
    @5
    simpr3
    #
    @3
    @4
    wa
    #
    @5
    @38
    @44
    @8
    cc0
    cY
    cc0
    @44
    @8
    cc0
    wceq
    #
    cY
    cc0
    wceq
    #
    @44
    @45
    cX
    cc0
    wceq
    @46
    cX
    cY
    gcdeq0
    simplbda
    ex
    necon3d
    imp
    syl21anc
    #
    @40
    @7
    @39
    @8
    cY
    cdvds
    wbr
    #
    @7
    @3
    @4
    @39
    @48
    wa
    @40
    @41
    cX
    cY
    gcddvds
    syl2anc
    #
    simpld
    @30
    @38
    @3
    w3a
    @39
    @28
    @8
    cX
    dvdsval2
    biimpa
    syl31anc
    #
    @7
    @30
    @38
    @4
    @48
    @29
    @42
    @47
    @41
    @7
    @39
    @48
    @49
    simprd
    @30
    @38
    @4
    w3a
    @48
    @29
    @8
    cY
    dvdsval2
    biimpa
    syl31anc
    #
    @42
    @7
    @32
    @12
    cB
    wcel
    #
    @12
    cR
    c0g
    cfv
    #
    wne
    #
    @7
    cz
    cB
    @11
    cL
    @7
    @27
    cz
    cB
    cL
    wf
    #
    @37
    cz
    cB
    zring
    cR
    cL
    zringbas
    qqhval2.0
    rhmf
    syl
    #
    @51
    ffvelrnd
    @7
    cL
    cz
    wfn
    #
    @29
    @11
    cL
    ccnv
    @53
    csn
    #
    cima
    #
    wcel
    #
    wn
    #
    @54
    @7
    @55
    @57
    @56
    cz
    cB
    cL
    ffn
    syl
    #
    @51
    @7
    @59
    cc0
    csn
    #
    @11
    @7
    @11
    cc0
    wne
    @11
    @63
    wcel
    #
    wn
    @7
    cY
    @8
    @7
    cY
    @41
    zcnd
    #
    @7
    @8
    @42
    zcnd
    #
    @43
    @47
    divne0d
    @64
    @11
    cc0
    @11
    cc0
    cY
    @8
    cdiv
    ovex
    elsn
    necon3bbii
    sylibr
    @7
    @35
    @1
    @59
    @63
    wceq
    #
    @0
    @35
    @1
    @6
    @36
    ad2antrr
    @0
    @1
    @6
    simplr
    @35
    @1
    @67
    cB
    cR
    cL
    @53
    qqhval2.0
    qqhval2.2
    @53
    eqid
    #
    zrhker
    biimpa
    syl2anc
    #
    neleqtrrd
    @57
    @29
    wa
    #
    @61
    wa
    @12
    @58
    wcel
    #
    wn
    @54
    @70
    @71
    @60
    @70
    @60
    @71
    @57
    @60
    @29
    @71
    cz
    @11
    @58
    cL
    elpreima
    baibd
    biimprd
    con3dimp
    @71
    @12
    @53
    @12
    @53
    @11
    cL
    fvex
    elsn
    necon3bbii
    sylib
    syl21anc
    @0
    @32
    @52
    @54
    wa
    wb
    @1
    @6
    cB
    cR
    @31
    @12
    @53
    qqhval2.0
    @31
    eqid
    #
    @68
    drngunit
    ad2antrr
    mpbir2and
    #
    @7
    @34
    @33
    cB
    wcel
    #
    @33
    @53
    wne
    #
    @7
    cz
    cB
    @8
    cL
    @56
    @42
    ffvelrnd
    @7
    @57
    @30
    @8
    @59
    wcel
    #
    wn
    #
    @75
    @62
    @42
    @7
    @59
    @63
    @8
    @7
    @38
    @8
    @63
    wcel
    #
    wn
    @47
    @78
    @8
    cc0
    @8
    cc0
    cX
    cY
    cgcd
    ovex
    elsn
    necon3bbii
    sylibr
    @69
    neleqtrrd
    @57
    @30
    wa
    #
    @77
    wa
    @33
    @58
    wcel
    #
    wn
    @75
    @79
    @80
    @76
    @79
    @76
    @80
    @57
    @76
    @30
    @80
    cz
    @8
    @58
    cL
    elpreima
    baibd
    biimprd
    con3dimp
    @80
    @33
    @53
    @33
    @53
    @8
    cL
    fvex
    elsn
    necon3bbii
    sylib
    syl21anc
    @0
    @34
    @74
    @75
    wa
    wb
    @1
    @6
    cB
    cR
    @31
    @33
    @53
    qqhval2.0
    @72
    @68
    drngunit
    ad2antrr
    mpbir2and
    @9
    @11
    @8
    c.dv
    zring
    cR
    cmul
    @31
    cL
    cz
    @72
    zringbas
    qqhval2.1
    zringmulr
    rhmdvd
    syl132anc
    @7
    cY
    cn
    wcel
    #
    @13
    @24
    wceq
    cY
    cneg
    cn
    wcel
    #
    @7
    @81
    wa
    #
    @10
    @21
    @12
    @23
    c.dv
    @83
    @9
    @20
    cL
    @83
    @20
    @9
    @83
    @20
    @9
    wceq
    #
    @22
    @11
    wceq
    #
    @7
    @3
    @81
    @84
    @85
    wa
    @40
    cX
    cY
    divnumden
    sylan
    #
    simpld
    eqcomd
    fveq2d
    @83
    @11
    @22
    cL
    @83
    @22
    @11
    @83
    @84
    @85
    @86
    simprd
    eqcomd
    fveq2d
    oveq12d
    @7
    @82
    wa
    #
    @9
    cneg
    #
    cL
    cfv
    #
    @11
    cneg
    #
    cL
    cfv
    #
    c.dv
    co
    @9
    c1
    cneg
    #
    cmul
    co
    #
    cL
    cfv
    #
    @11
    @92
    cmul
    co
    #
    cL
    cfv
    #
    c.dv
    co
    #
    @24
    @13
    @87
    @89
    @94
    @91
    @96
    c.dv
    @87
    @88
    @93
    cL
    @87
    @92
    @9
    cmul
    co
    @88
    @93
    @87
    @9
    @87
    @9
    @7
    @28
    @82
    @50
    adantr
    #
    zcnd
    #
    mulm1d
    @87
    @92
    @9
    @92
    cc
    wcel
    @87
    neg1cn
    a1i
    #
    @99
    mulcomd
    eqtr3d
    fveq2d
    @87
    @90
    @95
    cL
    @87
    @92
    @11
    cmul
    co
    @90
    @95
    @87
    @11
    @87
    @11
    @7
    @29
    @82
    @51
    adantr
    #
    zcnd
    #
    mulm1d
    @87
    @92
    @11
    @100
    @102
    mulcomd
    eqtr3d
    fveq2d
    oveq12d
    @87
    @21
    @89
    @23
    @91
    c.dv
    @87
    @20
    @88
    cL
    @87
    @20
    @88
    wceq
    #
    @22
    @90
    wceq
    #
    @87
    @3
    @4
    @82
    @103
    @104
    wa
    @7
    @3
    @82
    @40
    adantr
    @7
    @4
    @82
    @41
    adantr
    @7
    @82
    simpr
    cX
    cY
    divnumden2
    syl3anc
    #
    simpld
    fveq2d
    @87
    @22
    @90
    cL
    @87
    @103
    @104
    @105
    simprd
    fveq2d
    oveq12d
    @87
    @27
    @28
    @29
    @92
    cz
    wcel
    #
    @32
    @92
    cL
    cfv
    @31
    wcel
    #
    @13
    @97
    wceq
    @7
    @27
    @82
    @37
    adantr
    #
    @98
    @101
    @87
    c1
    @87
    1zzd
    znegcld
    @7
    @32
    @82
    @73
    adantr
    @87
    @27
    @92
    zring
    cui
    cfv
    wcel
    #
    @107
    @108
    @109
    @87
    @109
    @106
    @92
    cabs
    cfv
    #
    c1
    wceq
    neg1z
    @110
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    @92
    zringunit
    mpbir2an
    a1i
    @92
    zring
    cR
    cL
    elrhmunit
    syl2anc
    @9
    @11
    @92
    c.dv
    zring
    cR
    cmul
    @31
    cL
    cz
    @72
    zringbas
    qqhval2.1
    zringmulr
    rhmdvd
    syl132anc
    3eqtr4rd
    @6
    @81
    @82
    wo
    #
    @2
    @6
    @46
    wn
    @46
    @111
    wo
    #
    @111
    @6
    cY
    cc0
    @3
    @4
    @5
    simp3
    neneqd
    @6
    @46
    @81
    @82
    w3o
    #
    @112
    @6
    cY
    cr
    wcel
    #
    @113
    @6
    @4
    @114
    @113
    wa
    @3
    @4
    @5
    simp2
    cY
    elz
    sylib
    simprd
    @46
    @81
    @82
    3orass
    sylib
    @46
    @111
    orel1
    sylc
    adantl
    mpjaodan
    @7
    @15
    @25
    @17
    @26
    c.dv
    @7
    @14
    cX
    cL
    @7
    cX
    @8
    @7
    cX
    @40
    zcnd
    @66
    @47
    divcan1d
    fveq2d
    @7
    @16
    cY
    cL
    @7
    cY
    @8
    @65
    @66
    @47
    divcan1d
    fveq2d
    oveq12d
    3eqtr3d
end
