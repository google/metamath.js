include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cn0.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cmin.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "ccmn.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "pmatring.mm"
include "syl.mm"
include "ringcmn.mm"
include "adantr.mm"
include "nn0ex.mm"
include "a1i.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "3jca.mm"
include "chfacfscmulcl.mm"
include "chfacfscmulfsupp.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "nn0disj.mm"
include "cun.mm"
include "nnnn0.mm"
include "peano2nn0.mm"
include "nn0split.mm"
include "ad2antrl.mm"
include "gsumsplit2.mm"
include "c2.mm"
include "cc.mm"
include "nncn.mm"
include "add1p1.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "chfacfscmul0.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "sylan2.mm"
include "ringmnd.mm"
include "fvex.mm"
include "jctir.mm"
include "gsumz.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "elfznn0.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "mndrid.mm"
include "syl2anc.mm"
include "csn.mm"
include "gsummptfzsplit.mm"
include "gsummptfzsplitl.mm"
include "0nn0.mm"
include "mpd3an3.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "gsumsn.mm"
include "ovexd.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "elfznn.mm"
include "nnnn0d.mm"
include "adantl.mm"
include "mndass.mm"
include "syl13anc.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "wne.mm"
include "nnne0d.mm"
include "ad2antlr.mm"
include "wb.mm"
include "neeq1.mm"
include "mpbird.mm"
include "eqneqall.mm"
include "mpan9.mm"
include "eqeq1.mm"
include "eqcoms.mm"
include "wn.mm"
include "cz.mm"
include "cle.mm"
include "elfz2.mm"
include "wo.mm"
include "wi.mm"
include "zleltp1.mm"
include "ancoms.mm"
include "3adant1.mm"
include "biimpcd.mm"
include "impcom.mm"
include "orcd.mm"
include "cr.mm"
include "zre.mm"
include "1red.mm"
include "readdcld.mm"
include "anim12ci.mm"
include "lttri2.mm"
include "sylbi.mm"
include "neneqd.mm"
include "pm2.21d.mm"
include "imp.mm"
include "nnred.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "nn0red.mm"
include "ad2antrr.mm"
include "breq1.mm"
include "ltnsymd.mm"
include "simp-4r.mm"
include "oveq1d.mm"
include "ifeqda.mm"
include "fvmptd.mm"
include "nn0p1gt0.mm"
include "0red.mm"
include "ltne.mm"
include "sylan.mm"
include "mpdan.mm"
include "iftrue.mm"
include "fvexd.mm"
include "csca.mm"
include "cur.mm"
include "3ad2ant2.mm"
include "vr1cl.mm"
include "cmgp.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mulg0.mm"
include "ply1crng.mm"
include "matsca2.mm"
include "clmod.mm"
include "pmatlmod.mm"
include "wf.mm"
include "chfacfisf.mm"
include "syl3anl2.mm"
include "ffvelrnd.mm"
include "lmodvs1.mm"
include "3eqtrd.mm"
include "cmncom.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "eqeltrrd.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "simpl1.mm"
include "elmapi.mm"
include "0elfz.mm"
include "ringcl.mm"
include "grpsubadd0sub.mm"
include "3eqtr4d.mm"

theorem chfacfscmulgsum
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let vi: setvar i
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  let cK: class K
  let vz: setvar z
  assume chfacfisf.a: |- A = ( N Mat R )
  assume chfacfisf.b: |- B = ( Base ` A )
  assume chfacfisf.p: |- P = ( Poly1 ` R )
  assume chfacfisf.y: |- Y = ( N Mat P )
  assume chfacfisf.r: |- .X. = ( .r ` Y )
  assume chfacfisf.s: |- .- = ( -g ` Y )
  assume chfacfisf.0: |- .0. = ( 0g ` Y )
  assume chfacfisf.t: |- T = ( N matToPolyMat R )
  assume chfacfisf.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume chfacfscmulcl.x: |- X = ( var1 ` R )
  assume chfacfscmulcl.m: |- .x. = ( .s ` Y )
  assume chfacfscmulcl.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume chfacfscmulgsum.p: |- .+ = ( +g ` Y )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  disjoint B s
  disjoint .0. n
  disjoint B i
  disjoint i s
  disjoint G i
  disjoint M i
  disjoint N i
  disjoint R i
  disjoint X i
  disjoint Y i
  disjoint .^ i
  disjoint .x. b
  disjoint .x. i
  disjoint b i
  disjoint T n
  disjoint .- n
  disjoint .X. n
  disjoint i n
  disjoint B k
  disjoint B l
  disjoint k l
  disjoint M k
  disjoint M l
  disjoint N k
  disjoint N l
  disjoint R k
  disjoint R l
  disjoint T k
  disjoint T l
  disjoint Y k
  disjoint Y l
  disjoint b k
  disjoint b l
  disjoint k n
  disjoint k s
  disjoint l n
  disjoint l s
  disjoint .X. k
  disjoint .X. l
  disjoint .0. k
  disjoint .0. l
  disjoint .- k
  disjoint .- l
  disjoint K n
  disjoint B z
  disjoint k z
  disjoint s z
  disjoint G k
  disjoint G z
  disjoint i k
  disjoint i z
  disjoint M z
  disjoint N z
  disjoint R z
  disjoint X k
  disjoint X z
  disjoint .0. z
  disjoint .^ k
  disjoint .^ z
  disjoint .x. k
  disjoint .x. z
  disjoint b z
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( Y gsum ( i e. NN0 |-> ( ( i .^ X ) .x. ( G ` i ) ) ) ) = ( ( Y gsum ( i e. ( 1 ... s ) |-> ( ( i .^ X ) .x. ( ( T ` ( b ` ( i - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` i ) ) ) ) ) ) ) .+ ( ( ( ( s + 1 ) .^ X ) .x. ( T ` ( b ` s ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    cn
    wcel
    #
    vb
    cv
    #
    cB
    cc0
    @4
    cfz
    co
    #
    cmap
    co
    wcel
    #
    wa
    #
    wa
    #
    cY
    vi
    cn0
    vi
    cv
    #
    cX
    c.ex
    co
    #
    @11
    cG
    cfv
    #
    c.x
    co
    #
    cmpt
    cgsu
    co
    cY
    vi
    cc0
    @4
    c1
    caddc
    co
    #
    cfz
    co
    #
    @14
    cmpt
    cgsu
    co
    #
    cY
    vi
    @15
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @14
    cmpt
    #
    cgsu
    co
    #
    c.pl
    co
    #
    @17
    cY
    vi
    c1
    @4
    cfz
    co
    #
    @12
    @11
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cT
    cfv
    #
    cM
    cT
    cfv
    #
    @11
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @15
    cX
    c.ex
    co
    #
    @4
    @6
    cfv
    #
    cT
    cfv
    #
    c.x
    co
    #
    @27
    cc0
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    c.pl
    co
    #
    @10
    cn0
    cY
    cbs
    cfv
    #
    @16
    @19
    c.pl
    vi
    cY
    cvv
    @14
    c.0
    @44
    eqid
    #
    chfacfisf.0
    chfacfscmulgsum.p
    @3
    cY
    ccmn
    wcel
    #
    @9
    @3
    cY
    crg
    wcel
    #
    @46
    @3
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @47
    @0
    @1
    @49
    @2
    @1
    @48
    @0
    cR
    crngring
    #
    anim2i
    3adant3
    cY
    cP
    cR
    cN
    chfacfisf.p
    chfacfisf.y
    pmatring
    #
    syl
    #
    cY
    ringcmn
    syl
    adantr
    #
    cn0
    cvv
    wcel
    @10
    nn0ex
    a1i
    @10
    @11
    cn0
    wcel
    #
    wa
    #
    @3
    @9
    @54
    w3a
    #
    @14
    @44
    wcel
    #
    @55
    @3
    @9
    @54
    @3
    @9
    @54
    simpll
    @3
    @9
    @54
    simplr
    @10
    @54
    simpr
    3jca
    #
    cA
    cB
    cP
    cR
    cT
    c.x
    c.xp
    vn
    c.ex
    cG
    @11
    cM
    c.mi
    cN
    cX
    cY
    c.0
    vs
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.r
    chfacfisf.s
    chfacfisf.0
    chfacfisf.t
    chfacfisf.g
    chfacfscmulcl.x
    chfacfscmulcl.m
    chfacfscmulcl.e
    chfacfscmulcl
    #
    syl
    #
    cA
    cB
    cP
    cR
    cT
    c.x
    c.xp
    vi
    vn
    c.ex
    cG
    cM
    c.mi
    cN
    cX
    cY
    c.0
    vs
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.r
    chfacfisf.s
    chfacfisf.0
    chfacfisf.t
    chfacfisf.g
    chfacfscmulcl.x
    chfacfscmulcl.m
    chfacfscmulcl.e
    chfacfscmulfsupp
    @16
    @19
    cin
    c0
    wceq
    @10
    @15
    nn0disj
    a1i
    @5
    cn0
    @16
    @19
    cun
    wceq
    #
    @3
    @8
    @5
    @15
    cn0
    wcel
    #
    @61
    @5
    @4
    cn0
    wcel
    #
    @62
    @4
    nnnn0
    #
    @4
    peano2nn0
    #
    syl
    @15
    nn0split
    syl
    ad2antrl
    gsumsplit2
    @10
    @22
    @17
    c.0
    c.pl
    co
    #
    @17
    @10
    @21
    c.0
    @17
    c.pl
    @10
    @21
    cY
    vi
    @19
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @10
    @20
    @67
    cY
    cgsu
    @10
    vi
    @19
    @14
    c.0
    @10
    @11
    @19
    wcel
    #
    wa
    @3
    @9
    @11
    @4
    c2
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @14
    c.0
    wceq
    @3
    @9
    @69
    simpll
    @3
    @9
    @69
    simplr
    @10
    @69
    @72
    @10
    @19
    @71
    @11
    @10
    @18
    @70
    cuz
    @5
    @18
    @70
    wceq
    #
    @3
    @8
    @5
    @4
    cc
    wcel
    @73
    @4
    nncn
    @4
    add1p1
    syl
    ad2antrl
    fveq2d
    eleq2d
    biimpa
    cA
    cB
    cP
    cR
    cT
    c.x
    c.xp
    vn
    c.ex
    cG
    @11
    cM
    c.mi
    cN
    cX
    cY
    c.0
    vs
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.r
    chfacfisf.s
    chfacfisf.0
    chfacfisf.t
    chfacfisf.g
    chfacfscmulcl.x
    chfacfscmulcl.m
    chfacfscmulcl.e
    chfacfscmul0
    syl3anc
    mpteq2dva
    oveq2d
    @10
    cY
    cmnd
    wcel
    #
    @19
    cvv
    wcel
    #
    wa
    #
    @68
    c.0
    wceq
    @3
    @76
    @9
    @3
    @74
    @75
    @0
    @1
    @74
    @2
    @0
    @1
    wa
    @47
    @74
    @1
    @0
    @48
    @47
    @50
    @51
    sylan2
    cY
    ringmnd
    syl
    3adant3
    #
    @18
    cuz
    fvex
    jctir
    adantr
    @19
    vi
    cY
    cvv
    c.0
    chfacfisf.0
    gsumz
    syl
    eqtrd
    oveq2d
    @10
    @74
    @17
    @44
    wcel
    @66
    @17
    wceq
    @3
    @74
    @9
    @77
    adantr
    #
    @10
    @44
    vi
    cY
    @16
    @14
    @45
    @53
    @10
    cc0
    @15
    fzfid
    @10
    @57
    vi
    @16
    @10
    @11
    @16
    wcel
    #
    wa
    @56
    @57
    @79
    @10
    @54
    @56
    @11
    @15
    elfznn0
    @58
    sylan2
    @59
    syl
    #
    ralrimiva
    gsummptcl
    @44
    c.pl
    cY
    @17
    c.0
    @45
    chfacfscmulgsum.p
    chfacfisf.0
    mndrid
    syl2anc
    eqtrd
    @10
    @17
    cY
    vi
    @7
    @14
    cmpt
    cgsu
    co
    #
    cY
    vi
    @15
    csn
    @14
    cmpt
    cgsu
    co
    #
    c.pl
    co
    cY
    vi
    @23
    @14
    cmpt
    #
    cgsu
    co
    #
    cc0
    cX
    c.ex
    co
    #
    cc0
    cG
    cfv
    #
    c.x
    co
    #
    c.pl
    co
    #
    @35
    @15
    cG
    cfv
    #
    c.x
    co
    #
    c.pl
    co
    #
    @43
    @10
    @44
    c.pl
    vi
    cY
    @4
    @14
    @45
    chfacfscmulgsum.p
    @53
    @5
    @63
    @3
    @8
    @64
    ad2antrl
    #
    @80
    gsummptfzsplit
    @10
    @81
    @88
    @82
    @90
    c.pl
    @10
    @81
    @84
    cY
    vi
    cc0
    csn
    @14
    cmpt
    cgsu
    co
    #
    c.pl
    co
    @88
    @10
    @44
    c.pl
    vi
    cY
    @4
    @14
    @45
    chfacfscmulgsum.p
    @53
    @92
    @11
    @7
    wcel
    @10
    @54
    @57
    @11
    @4
    elfznn0
    @60
    sylan2
    gsummptfzsplitl
    @10
    @93
    @87
    @84
    c.pl
    @10
    @74
    cc0
    cn0
    wcel
    #
    @87
    @44
    wcel
    #
    @93
    @87
    wceq
    @78
    @94
    @10
    0nn0
    a1i
    #
    @3
    @9
    @94
    @95
    @96
    cA
    cB
    cP
    cR
    cT
    c.x
    c.xp
    vn
    c.ex
    cG
    cc0
    cM
    c.mi
    cN
    cX
    cY
    c.0
    vs
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.r
    chfacfisf.s
    chfacfisf.0
    chfacfisf.t
    chfacfisf.g
    chfacfscmulcl.x
    chfacfscmulcl.m
    chfacfscmulcl.e
    chfacfscmulcl
    mpd3an3
    #
    @14
    @44
    @87
    vi
    cY
    cc0
    cn0
    @45
    @11
    cc0
    wceq
    @12
    @85
    @13
    @86
    c.x
    @11
    cc0
    cX
    c.ex
    oveq1
    @11
    cc0
    cG
    fveq2
    oveq12d
    gsumsn
    syl3anc
    oveq2d
    eqtrd
    @10
    @74
    @15
    cvv
    wcel
    @90
    @44
    wcel
    #
    @82
    @90
    wceq
    @78
    @10
    @4
    c1
    caddc
    ovexd
    @3
    @9
    @62
    @98
    @10
    @4
    c1
    @92
    c1
    cn0
    wcel
    @10
    1nn0
    a1i
    nn0addcld
    cA
    cB
    cP
    cR
    cT
    c.x
    c.xp
    vn
    c.ex
    cG
    @15
    cM
    c.mi
    cN
    cX
    cY
    c.0
    vs
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.r
    chfacfisf.s
    chfacfisf.0
    chfacfisf.t
    chfacfisf.g
    chfacfscmulcl.x
    chfacfscmulcl.m
    chfacfscmulcl.e
    chfacfscmulcl
    mpd3an3
    #
    @14
    @44
    @90
    vi
    cY
    @15
    cvv
    @45
    @11
    @15
    wceq
    @12
    @35
    @13
    @89
    c.x
    @11
    @15
    cX
    c.ex
    oveq1
    @11
    @15
    cG
    fveq2
    oveq12d
    gsumsn
    syl3anc
    oveq12d
    @10
    @91
    @84
    @87
    @90
    c.pl
    co
    #
    c.pl
    co
    #
    @43
    @10
    @74
    @84
    @44
    wcel
    @95
    @98
    @91
    @101
    wceq
    @78
    @10
    @44
    vi
    cY
    @23
    @14
    @45
    @53
    @10
    c1
    @4
    fzfid
    @10
    @57
    vi
    @23
    @10
    @11
    @23
    wcel
    #
    wa
    #
    @3
    @9
    @54
    @57
    @3
    @9
    @102
    simpll
    @3
    @9
    @102
    simplr
    @102
    @54
    @10
    @102
    @11
    @11
    @4
    elfznn
    #
    nnnn0d
    adantl
    #
    @59
    syl3anc
    ralrimiva
    gsummptcl
    @97
    @99
    @44
    c.pl
    cY
    @84
    @87
    @90
    @45
    chfacfscmulgsum.p
    mndass
    syl13anc
    @10
    @84
    @34
    @100
    @42
    c.pl
    @10
    @83
    @33
    cY
    cgsu
    @10
    vi
    @23
    @14
    @32
    @103
    @13
    @31
    @12
    c.x
    @103
    vn
    @11
    vn
    cv
    #
    cc0
    wceq
    #
    c.0
    @41
    c.mi
    co
    #
    @106
    @15
    wceq
    #
    @37
    @15
    @106
    clt
    wbr
    #
    c.0
    @106
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cT
    cfv
    #
    @27
    @106
    @6
    cfv
    #
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    #
    cif
    #
    cif
    #
    cif
    #
    @31
    cn0
    cG
    cvv
    cG
    vn
    cn0
    @120
    cmpt
    wceq
    #
    @103
    chfacfisf.g
    a1i
    @103
    @106
    @11
    wceq
    #
    wa
    #
    @107
    @108
    @119
    @31
    @123
    @107
    wa
    #
    c.0
    @26
    @41
    @30
    c.mi
    @123
    @106
    cc0
    wne
    #
    @107
    c.0
    @26
    wceq
    #
    @123
    @125
    @11
    cc0
    wne
    #
    @102
    @127
    @10
    @122
    @102
    @11
    @104
    nnne0d
    ad2antlr
    @122
    @125
    @127
    wb
    @103
    @106
    @11
    cc0
    neeq1
    adantl
    mpbird
    @126
    @106
    cc0
    eqneqall
    mpan9
    @124
    @40
    @29
    @27
    c.xp
    @124
    @39
    @28
    cT
    @124
    cc0
    @11
    @6
    @124
    cc0
    @11
    wceq
    #
    @122
    @103
    @122
    @107
    simplr
    @107
    @128
    @122
    wb
    #
    @123
    @129
    cc0
    @106
    cc0
    @106
    @11
    eqeq1
    eqcoms
    adantl
    mpbird
    fveq2d
    fveq2d
    oveq2d
    oveq12d
    @123
    @107
    wn
    #
    wa
    #
    @109
    @37
    @118
    @31
    @131
    @109
    @37
    @31
    wceq
    #
    @131
    @109
    @132
    @131
    @106
    @15
    @123
    @106
    @15
    wne
    #
    @130
    @123
    @133
    @11
    @15
    wne
    #
    @102
    @134
    @10
    @122
    @102
    c1
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    w3a
    #
    c1
    @11
    cle
    wbr
    #
    @11
    @4
    cle
    wbr
    #
    wa
    #
    wa
    #
    @134
    @11
    c1
    @4
    elfz2
    #
    @142
    @134
    @11
    @15
    clt
    wbr
    #
    @15
    @11
    clt
    wbr
    #
    wo
    #
    @142
    @144
    @145
    @141
    @138
    @144
    @140
    @138
    @144
    wi
    @139
    @138
    @140
    @144
    @136
    @137
    @140
    @144
    wb
    #
    @135
    @137
    @136
    @147
    @11
    @4
    zleltp1
    ancoms
    3adant1
    biimpcd
    adantl
    impcom
    #
    orcd
    @138
    @134
    @146
    wb
    #
    @141
    @138
    @11
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    wa
    #
    @149
    @136
    @137
    @152
    @135
    @136
    @151
    @137
    @150
    @136
    @4
    c1
    @4
    zre
    @136
    1red
    readdcld
    @11
    zre
    anim12ci
    3adant1
    @11
    @15
    lttri2
    syl
    adantr
    mpbird
    sylbi
    ad2antlr
    @122
    @133
    @134
    wb
    @103
    @106
    @11
    @15
    neeq1
    adantl
    mpbird
    adantr
    neneqd
    pm2.21d
    imp
    @131
    @109
    wn
    #
    wa
    #
    @110
    c.0
    @117
    @31
    @154
    @110
    c.0
    @31
    wceq
    #
    @123
    @110
    @155
    wi
    @130
    @153
    @123
    @110
    @155
    @123
    @106
    @15
    @103
    @122
    @106
    cr
    wcel
    #
    @102
    @122
    @156
    wi
    @10
    @102
    @156
    @122
    @150
    @102
    @11
    @104
    nnred
    @106
    @11
    cr
    eleq1
    syl5ibrcom
    adantl
    imp
    @123
    @4
    c1
    @10
    @4
    cr
    wcel
    @102
    @122
    @10
    @4
    @92
    nn0red
    ad2antrr
    @123
    1red
    readdcld
    @123
    @106
    @15
    clt
    wbr
    #
    @144
    @102
    @144
    @10
    @122
    @102
    @142
    @144
    @143
    @148
    sylbi
    ad2antlr
    @122
    @157
    @144
    wb
    @103
    @106
    @11
    @15
    clt
    breq1
    adantl
    mpbird
    ltnsymd
    pm2.21d
    ad2antrr
    imp
    @154
    @110
    wn
    #
    wa
    #
    @113
    @26
    @116
    @30
    c.mi
    @159
    @112
    @25
    cT
    @159
    @111
    @24
    @6
    @159
    @106
    @11
    c1
    cmin
    @103
    @122
    @130
    @153
    @158
    simp-4r
    #
    oveq1d
    fveq2d
    fveq2d
    @159
    @115
    @29
    @27
    c.xp
    @159
    @114
    @28
    cT
    @159
    @106
    @11
    @6
    @160
    fveq2d
    fveq2d
    oveq2d
    oveq12d
    ifeqda
    ifeqda
    ifeqda
    @105
    @103
    @26
    @30
    c.mi
    ovexd
    fvmptd
    oveq2d
    mpteq2dva
    oveq2d
    @10
    @90
    @87
    c.pl
    co
    #
    @38
    @108
    c.pl
    co
    #
    @100
    @42
    @10
    @90
    @38
    @87
    @108
    c.pl
    @10
    @89
    @37
    @35
    c.x
    @10
    vn
    @15
    @120
    @37
    cn0
    cG
    cvv
    @121
    @10
    chfacfisf.g
    a1i
    #
    @10
    @109
    wa
    #
    @107
    @108
    @119
    @37
    @164
    @125
    @107
    @108
    @37
    wceq
    #
    @10
    @109
    @125
    @5
    @109
    @125
    wi
    #
    @3
    @8
    @5
    @63
    @166
    @64
    @63
    cc0
    @15
    clt
    wbr
    #
    @166
    @4
    nn0p1gt0
    @63
    @167
    wa
    @125
    @109
    @15
    cc0
    wne
    #
    @63
    cc0
    cr
    wcel
    @167
    @168
    @63
    0red
    cc0
    @15
    ltne
    sylan
    @106
    @15
    cc0
    neeq1
    syl5ibrcom
    mpdan
    syl
    ad2antrl
    imp
    @165
    @106
    cc0
    eqneqall
    mpan9
    @109
    @119
    @37
    wceq
    @10
    @130
    @109
    @37
    @118
    iftrue
    ad2antlr
    ifeqda
    @10
    @63
    @62
    @92
    @65
    syl
    @10
    @36
    cT
    fvexd
    fvmptd
    oveq2d
    #
    @10
    @87
    cY
    csca
    cfv
    #
    cur
    cfv
    #
    @86
    c.x
    co
    #
    @86
    @108
    @10
    @85
    @171
    @86
    c.x
    @3
    @85
    @171
    wceq
    @9
    @3
    @85
    cP
    cur
    cfv
    #
    @171
    @3
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    @85
    @173
    wceq
    @3
    @48
    @175
    @1
    @0
    @48
    @2
    @50
    3ad2ant2
    #
    @174
    cP
    cR
    cX
    chfacfscmulcl.x
    chfacfisf.p
    @174
    eqid
    #
    vr1cl
    syl
    @174
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    @173
    @174
    cP
    @178
    @178
    eqid
    #
    @177
    mgpbas
    cP
    @173
    @178
    @179
    @173
    eqid
    ringidval
    chfacfscmulcl.e
    mulg0
    syl
    @3
    cP
    @170
    cur
    @3
    @0
    cP
    ccrg
    wcel
    #
    wa
    #
    cP
    @170
    wceq
    @0
    @1
    @181
    @2
    @1
    @180
    @0
    cP
    cR
    chfacfisf.p
    ply1crng
    anim2i
    3adant3
    cY
    cP
    cN
    ccrg
    chfacfisf.y
    matsca2
    syl
    fveq2d
    eqtrd
    adantr
    oveq1d
    @10
    cY
    clmod
    wcel
    #
    @86
    @44
    wcel
    @172
    @86
    wceq
    @3
    @182
    @9
    @0
    @1
    @182
    @2
    @1
    @0
    @48
    @182
    @50
    cY
    cP
    cR
    cN
    chfacfisf.p
    chfacfisf.y
    pmatlmod
    sylan2
    3adant3
    adantr
    @10
    cn0
    @44
    cc0
    cG
    @1
    @0
    @48
    @2
    @9
    cn0
    @44
    cG
    wf
    @50
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.r
    chfacfisf.s
    chfacfisf.0
    chfacfisf.t
    chfacfisf.g
    chfacfisf
    syl3anl2
    @96
    ffvelrnd
    c.x
    @171
    @170
    @44
    cY
    @86
    @45
    @170
    eqid
    chfacfscmulcl.m
    @171
    eqid
    lmodvs1
    syl2anc
    @10
    vn
    cc0
    @120
    @108
    cn0
    cG
    cvv
    @163
    @107
    @120
    @108
    wceq
    @10
    @107
    @108
    @119
    iftrue
    adantl
    @96
    @10
    c.0
    @41
    c.mi
    ovexd
    fvmptd
    3eqtrd
    oveq12d
    @10
    @46
    @95
    @98
    @100
    @161
    wceq
    @53
    @97
    @99
    @44
    c.pl
    cY
    @87
    @90
    @45
    chfacfscmulgsum.p
    cmncom
    syl3anc
    @10
    cY
    cgrp
    wcel
    #
    @38
    @44
    wcel
    @41
    @44
    wcel
    #
    @42
    @162
    wceq
    @3
    @183
    @9
    @3
    @47
    @183
    @52
    cY
    ringgrp
    syl
    adantr
    @10
    @90
    @38
    @44
    @169
    @99
    eqeltrrd
    @10
    @47
    @27
    @44
    wcel
    #
    @40
    @44
    wcel
    #
    @184
    @3
    @47
    @9
    @52
    adantr
    @3
    @185
    @9
    @1
    @0
    @48
    @2
    @185
    @50
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    mat2pmatbas
    syl3an2
    adantr
    @10
    @0
    @48
    @39
    cB
    wcel
    @186
    @0
    @1
    @2
    @9
    simpl1
    @3
    @48
    @9
    @176
    adantr
    @10
    @7
    cB
    cc0
    @6
    @9
    @7
    cB
    @6
    wf
    #
    @3
    @8
    @187
    @5
    @6
    cB
    @7
    elmapi
    adantl
    adantl
    @5
    cc0
    @7
    wcel
    #
    @3
    @8
    @5
    @63
    @188
    @64
    @4
    0elfz
    syl
    ad2antrl
    ffvelrnd
    cA
    cB
    cY
    cP
    cR
    cT
    @39
    cN
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    mat2pmatbas
    syl3anc
    @44
    cY
    c.xp
    @27
    @40
    @45
    chfacfisf.r
    ringcl
    syl3anc
    @44
    c.pl
    cY
    c.mi
    @38
    @41
    c.0
    @45
    chfacfisf.0
    chfacfisf.s
    chfacfscmulgsum.p
    grpsubadd0sub
    syl3anc
    3eqtr4d
    oveq12d
    eqtrd
    3eqtrd
    3eqtrd
end
