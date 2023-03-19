include "chlt.mm"
include "wcel.mm"
include "cp0.mm"
include "cfv.mm"
include "cv.mm"
include "cplt.mm"
include "wbr.mm"
include "wa.mm"
include "cp1.mm"
include "cbs.mm"
include "wrex.mm"
include "co.mm"
include "eqid.mm"
include "hlhgt4.mm"
include "wi.mm"
include "w3a.mm"
include "cple.mm"
include "simpl1.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "3syl.mm"
include "simpl2l.mm"
include "simprll.mm"
include "hlrelat3.mm"
include "syl31anc.mm"
include "wb.mm"
include "simp11.mm"
include "simp3.mm"
include "atcvr0.mm"
include "syl2anc.mm"
include "col.mm"
include "wceq.mm"
include "hlol.mm"
include "syl.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "olj02.mm"
include "breqtrrd.mm"
include "biantrurd.mm"
include "breq1d.mm"
include "bitr3d.mm"
include "3expa.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "3adant3r.mm"
include "simp12r.mm"
include "simp3r.mm"
include "simp2lr.mm"
include "cpo.mm"
include "hlpos.mm"
include "simp12l.mm"
include "plelttr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "clat.mm"
include "hllat.mm"
include "simp3ll.mm"
include "simp3lr.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp12.mm"
include "simp1ll.mm"
include "simp2ll.mm"
include "simp3l.mm"
include "op1cl.mm"
include "simp1r.mm"
include "simp1lr.mm"
include "simpl.mm"
include "reximi.mm"
include "3exp.mm"
include "exp4a.mm"
include "ex.mm"
include "3adant2.mm"
include "3imp.mm"
include "3adant2l.mm"
include "imp.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"
include "3imp1.mm"
include "3expia.mm"
include "expd.mm"
include "reximdvai.mm"
include "3exp1.mm"
include "rexlimdv.mm"
include "rexlimdvva.mm"

theorem athgt
  let cA: class A
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume athgt.j: |- .\/ = ( join ` K )
  assume athgt.c: |- C = ( <o ` K )
  assume athgt.a: |- A = ( Atoms ` K )

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint A q
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint .\/ r
  disjoint .\/ s
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint K s
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K x
  disjoint K y
  disjoint K z
  assert |- ( K e. HL -> E. p e. A E. q e. A ( p C ( p .\/ q ) /\ E. r e. A ( ( p .\/ q ) C ( ( p .\/ q ) .\/ r ) /\ E. s e. A ( ( p .\/ q ) .\/ r ) C ( ( ( p .\/ q ) .\/ r ) .\/ s ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cK
    cp0
    cfv
    #
    vx
    cv
    #
    cK
    cplt
    cfv
    #
    wbr
    #
    @2
    vy
    cv
    #
    @3
    wbr
    #
    wa
    #
    @5
    vz
    cv
    #
    @3
    wbr
    #
    @8
    cK
    cp1
    cfv
    #
    @3
    wbr
    #
    wa
    #
    wa
    #
    vz
    cK
    cbs
    cfv
    #
    wrex
    #
    vy
    @14
    wrex
    vx
    @14
    wrex
    vp
    cv
    #
    @16
    vq
    cv
    #
    c.or
    co
    #
    cC
    wbr
    #
    @18
    @18
    vr
    cv
    #
    c.or
    co
    #
    cC
    wbr
    #
    @21
    @21
    vs
    cv
    c.or
    co
    #
    cC
    wbr
    #
    vs
    cA
    wrex
    #
    wa
    #
    vr
    cA
    wrex
    #
    wa
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    vx
    vy
    vz
    @14
    @3
    @10
    cK
    @1
    @14
    eqid
    #
    @3
    eqid
    #
    @1
    eqid
    #
    @10
    eqid
    #
    hlhgt4
    @0
    @15
    @30
    vx
    vy
    @14
    @14
    @0
    @2
    @14
    wcel
    #
    @5
    @14
    wcel
    #
    wa
    #
    wa
    @13
    @30
    vz
    @14
    @0
    @37
    @8
    @14
    wcel
    #
    @13
    @30
    wi
    wi
    @0
    @37
    @38
    @13
    @30
    @0
    @37
    @38
    w3a
    #
    @13
    wa
    #
    @16
    @2
    cK
    cple
    cfv
    #
    wbr
    #
    vp
    cA
    wrex
    #
    @30
    @40
    @1
    @1
    @16
    c.or
    co
    #
    cC
    wbr
    #
    @44
    @2
    @41
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    @43
    @40
    @0
    @1
    @14
    wcel
    #
    @35
    @4
    @48
    @0
    @37
    @38
    @13
    simpl1
    #
    @40
    @0
    cK
    cops
    wcel
    #
    @49
    @50
    cK
    hlop
    #
    @14
    cK
    @1
    @31
    @33
    op0cl
    3syl
    @35
    @36
    @0
    @38
    @13
    simpl2l
    @39
    @4
    @6
    @12
    simprll
    cA
    @14
    cC
    @3
    c.or
    cK
    @41
    @1
    @2
    vp
    @31
    @41
    eqid
    #
    @32
    athgt.j
    athgt.c
    athgt.a
    hlrelat3
    syl31anc
    @40
    @47
    @42
    vp
    cA
    @39
    @13
    @16
    cA
    wcel
    #
    @47
    @42
    wb
    @39
    @13
    @54
    w3a
    #
    @46
    @47
    @42
    @55
    @45
    @46
    @55
    @1
    @16
    @44
    cC
    @55
    @0
    @54
    @1
    @16
    cC
    wbr
    @0
    @37
    @38
    @13
    @54
    simp11
    #
    @39
    @13
    @54
    simp3
    cA
    cC
    chlt
    @16
    cK
    @1
    @33
    athgt.c
    athgt.a
    atcvr0
    syl2anc
    @55
    cK
    col
    wcel
    #
    @16
    @14
    wcel
    #
    @44
    @16
    wceq
    @55
    @0
    @57
    @56
    cK
    hlol
    syl
    @54
    @39
    @58
    @13
    cA
    @14
    @16
    cK
    @31
    athgt.a
    atbase
    #
    3ad2ant3
    #
    @14
    c.or
    cK
    @16
    @1
    @31
    athgt.j
    @33
    olj02
    syl2anc
    #
    breqtrrd
    biantrurd
    @55
    @44
    @16
    @2
    @41
    @61
    breq1d
    bitr3d
    3expa
    rexbidva
    mpbid
    @40
    @42
    @29
    vp
    cA
    @40
    @54
    @42
    @29
    @39
    @13
    @54
    @42
    wa
    #
    @29
    @39
    @13
    @62
    w3a
    #
    @19
    @18
    @5
    @41
    wbr
    #
    wa
    #
    vq
    cA
    wrex
    #
    @29
    @63
    @0
    @58
    @36
    @16
    @5
    @3
    wbr
    #
    @66
    @0
    @37
    @38
    @13
    @62
    simp11
    #
    @39
    @13
    @54
    @58
    @42
    @60
    3adant3r
    #
    @35
    @36
    @0
    @38
    @13
    @62
    simp12r
    #
    @63
    @42
    @6
    @67
    @39
    @13
    @54
    @42
    simp3r
    @4
    @6
    @12
    @39
    @62
    simp2lr
    @63
    cK
    cpo
    wcel
    #
    @58
    @35
    @36
    @42
    @6
    wa
    @67
    wi
    @63
    @0
    @71
    @68
    cK
    hlpos
    #
    syl
    @69
    @35
    @36
    @0
    @38
    @13
    @62
    simp12l
    @70
    @14
    @3
    cK
    @41
    @16
    @2
    @5
    @31
    @53
    @32
    plelttr
    syl13anc
    mp2and
    cA
    @14
    cC
    @3
    c.or
    cK
    @41
    @16
    @5
    vq
    @31
    @53
    @32
    athgt.j
    athgt.c
    athgt.a
    hlrelat3
    syl31anc
    @39
    @13
    @54
    @66
    @29
    wi
    #
    @42
    @39
    @12
    @54
    @73
    @7
    @39
    @12
    @54
    w3a
    #
    @65
    @28
    vq
    cA
    @74
    @17
    cA
    wcel
    #
    wa
    @64
    @27
    @19
    @39
    @12
    @54
    @75
    @64
    @27
    wi
    #
    @0
    @36
    @38
    @12
    @54
    @75
    @76
    wi
    wi
    wi
    @35
    @0
    @36
    @38
    w3a
    #
    @12
    @54
    @75
    @76
    @77
    @12
    @54
    @75
    wa
    #
    @64
    @27
    @77
    @12
    @78
    @64
    wa
    #
    @27
    @77
    @12
    @79
    w3a
    #
    @22
    @21
    @8
    @41
    wbr
    #
    wa
    #
    vr
    cA
    wrex
    #
    @27
    @80
    @0
    @18
    @14
    wcel
    #
    @38
    @18
    @8
    @3
    wbr
    #
    @83
    @0
    @36
    @38
    @12
    @79
    simp11
    #
    @80
    cK
    clat
    wcel
    #
    @58
    @17
    @14
    wcel
    #
    @84
    @80
    @0
    @87
    @86
    cK
    hllat
    #
    syl
    @80
    @54
    @58
    @54
    @75
    @64
    @77
    @12
    simp3ll
    @59
    syl
    @80
    @75
    @88
    @54
    @75
    @64
    @77
    @12
    simp3lr
    cA
    @14
    @17
    cK
    @31
    athgt.a
    atbase
    #
    syl
    @14
    c.or
    cK
    @16
    @17
    @31
    athgt.j
    latjcl
    #
    syl3anc
    #
    @0
    @36
    @38
    @12
    @79
    simp13
    #
    @80
    @64
    @9
    @85
    @77
    @12
    @78
    @64
    simp3r
    @77
    @9
    @11
    @79
    simp2l
    @80
    @71
    @84
    @36
    @38
    @64
    @9
    wa
    @85
    wi
    @80
    @0
    @71
    @86
    @72
    syl
    @92
    @0
    @36
    @38
    @12
    @79
    simp12
    @93
    @14
    @3
    cK
    @41
    @18
    @5
    @8
    @31
    @53
    @32
    plelttr
    syl13anc
    mp2and
    cA
    @14
    cC
    @3
    c.or
    cK
    @41
    @18
    @8
    vr
    @31
    @53
    @32
    athgt.j
    athgt.c
    athgt.a
    hlrelat3
    syl31anc
    @80
    @82
    @26
    vr
    cA
    @80
    @20
    cA
    wcel
    #
    wa
    @81
    @25
    @22
    @80
    @94
    @81
    @25
    wi
    #
    @77
    @11
    @79
    @94
    @95
    wi
    #
    @9
    @77
    @11
    @79
    @96
    @0
    @38
    @11
    @79
    @96
    wi
    #
    wi
    @36
    @0
    @38
    wa
    #
    @11
    @97
    @98
    @11
    wa
    #
    @79
    @94
    @81
    @25
    @99
    @79
    @94
    @81
    wa
    #
    @25
    @99
    @79
    @100
    w3a
    #
    @24
    @23
    @10
    @41
    wbr
    #
    wa
    #
    vs
    cA
    wrex
    #
    @25
    @101
    @0
    @21
    @14
    wcel
    #
    @10
    @14
    wcel
    #
    @21
    @10
    @3
    wbr
    #
    @104
    @0
    @38
    @11
    @79
    @100
    simp1ll
    #
    @101
    @87
    @84
    @20
    @14
    wcel
    #
    @105
    @101
    @0
    @87
    @108
    @89
    syl
    #
    @101
    @87
    @58
    @88
    @84
    @110
    @101
    @54
    @58
    @54
    @75
    @64
    @99
    @100
    simp2ll
    @59
    syl
    @101
    @75
    @88
    @54
    @75
    @64
    @99
    @100
    simp2lr
    @90
    syl
    @91
    syl3anc
    @101
    @94
    @109
    @99
    @79
    @94
    @81
    simp3l
    cA
    @14
    @20
    cK
    @31
    athgt.a
    atbase
    syl
    @14
    c.or
    cK
    @18
    @20
    @31
    athgt.j
    latjcl
    syl3anc
    #
    @101
    @0
    @51
    @106
    @108
    @52
    @14
    @10
    cK
    @31
    @34
    op1cl
    3syl
    #
    @101
    @81
    @11
    @107
    @99
    @79
    @94
    @81
    simp3r
    @98
    @11
    @79
    @100
    simp1r
    @101
    @71
    @105
    @38
    @106
    @81
    @11
    wa
    @107
    wi
    @101
    @0
    @71
    @108
    @72
    syl
    @111
    @0
    @38
    @11
    @79
    @100
    simp1lr
    @112
    @14
    @3
    cK
    @41
    @21
    @8
    @10
    @31
    @53
    @32
    plelttr
    syl13anc
    mp2and
    cA
    @14
    cC
    @3
    c.or
    cK
    @41
    @21
    @10
    vs
    @31
    @53
    @32
    athgt.j
    athgt.c
    athgt.a
    hlrelat3
    syl31anc
    @103
    @24
    vs
    cA
    @24
    @102
    simpl
    reximi
    syl
    3exp
    exp4a
    ex
    3adant2
    3imp
    3adant2l
    imp
    anim2d
    reximdva
    mpd
    3exp
    exp4a
    exp4a
    3adant2l
    3imp1
    anim2d
    reximdva
    3adant2l
    3adant3r
    mpd
    3expia
    expd
    reximdvai
    mpd
    3exp1
    imp
    rexlimdv
    rexlimdvva
    mpd
end
