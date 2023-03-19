include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "wrex.mm"
include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ply1mulgsumlem1.mm"
include "c2.mm"
include "cmul.mm"
include "2nn0.mm"
include "a1i.mm"
include "id.mm"
include "nn0mulcld.mm"
include "ad2antrr.mm"
include "wb.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "adantl.mm"
include "cle.mm"
include "cr.mm"
include "2re.mm"
include "nn0re.mm"
include "remulcld.mm"
include "adantr.mm"
include "elfznn0.mm"
include "syl.mm"
include "ltsub1d.mm"
include "lesub2d.mm"
include "resubcld.mm"
include "resubcl.mm"
include "syl2an.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "cc.mm"
include "nn0cn.mm"
include "2txmxeqx.mm"
include "breq1d.mm"
include "sylibd.mm"
include "expcomd.mm"
include "imp.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "imp41.mm"
include "impcom.mm"
include "fznn0sub2.mm"
include "breq2.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "simpr.mm"
include "syl6.mm"
include "3syl.mm"
include "com12.mm"
include "ad4antlr.mm"
include "mpd.mm"
include "oveq2d.mm"
include "cbs.mm"
include "simplr1.mm"
include "simplr2.mm"
include "anim12i.mm"
include "eqid.mm"
include "coe1fvalcl.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "wn.mm"
include "ltnle.mm"
include "bicomd.mm"
include "expcom.mm"
include "syl11.mm"
include "ad4antr.mm"
include "weq.mm"
include "simpl.mm"
include "oveq1d.mm"
include "simplr3.mm"
include "fznn0sub.mm"
include "ringlz.mm"
include "pm2.61ian.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "cvv.mm"
include "ringmnd.mm"
include "3ad2ant1.mm"
include "ovex.mm"
include "jctir.mm"
include "ad3antlr.mm"
include "gsumz.mm"
include "ralrimiva.mm"
include "rspcedvd.mm"
include "rexlimiva.mm"
include "mpcom.mm"

theorem ply1mulgsumlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vn: setvar n
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let vs: setvar s
  let vl: setvar l
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vz: setvar z
  let vk: setvar k
  assume ply1mulgsum.p: |- P = ( Poly1 ` R )
  assume ply1mulgsum.b: |- B = ( Base ` P )
  assume ply1mulgsum.a: |- A = ( coe1 ` K )
  assume ply1mulgsum.c: |- C = ( coe1 ` L )
  assume ply1mulgsum.x: |- X = ( var1 ` R )
  assume ply1mulgsum.pm: |- .X. = ( .r ` P )
  assume ply1mulgsum.sm: |- .x. = ( .s ` P )
  assume ply1mulgsum.rm: |- .* = ( .r ` R )
  assume ply1mulgsum.m: |- M = ( mulGrp ` P )
  assume ply1mulgsum.e: |- .^ = ( .g ` M )

  disjoint A n
  disjoint A s
  disjoint n s
  disjoint B n
  disjoint B s
  disjoint C n
  disjoint C s
  disjoint K n
  disjoint K s
  disjoint L n
  disjoint L s
  disjoint R n
  disjoint R s
  disjoint A l
  disjoint l n
  disjoint B l
  disjoint C l
  disjoint K l
  disjoint L l
  disjoint R l
  disjoint l s
  disjoint .* s
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a n
  disjoint a s
  disjoint b n
  disjoint b s
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint K a
  disjoint K b
  disjoint L a
  disjoint L b
  disjoint R a
  disjoint R b
  disjoint A x
  disjoint A z
  disjoint l x
  disjoint l z
  disjoint n x
  disjoint n z
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint K x
  disjoint K z
  disjoint L x
  disjoint L z
  disjoint R x
  disjoint R z
  disjoint s x
  disjoint s z
  disjoint .* z
  disjoint k x
  assert |- ( ( R e. Ring /\ K e. B /\ L e. B ) -> E. s e. NN0 A. n e. NN0 ( s < n -> ( R gsum ( l e. ( 0 ... n ) |-> ( ( A ` l ) .* ( C ` ( n - l ) ) ) ) ) = ( 0g ` R ) ) )

  proof
    vz
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    @1
    cA
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    @1
    cC
    cfv
    #
    @4
    wceq
    #
    wa
    #
    wi
    #
    vx
    cn0
    wral
    #
    vz
    cn0
    wrex
    cR
    crg
    wcel
    #
    cK
    cB
    wcel
    #
    cL
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    vn
    cv
    #
    clt
    wbr
    #
    cR
    vl
    cc0
    @16
    cfz
    co
    #
    vl
    cv
    #
    cA
    cfv
    #
    @16
    @19
    cmin
    co
    #
    cC
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @4
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    cA
    cB
    cC
    cP
    cR
    c.x
    c.xp
    vx
    c.ex
    c.as
    cK
    cL
    cM
    cX
    vz
    ply1mulgsum.p
    ply1mulgsum.b
    ply1mulgsum.a
    ply1mulgsum.c
    ply1mulgsum.x
    ply1mulgsum.pm
    ply1mulgsum.sm
    ply1mulgsum.rm
    ply1mulgsum.m
    ply1mulgsum.e
    ply1mulgsumlem1
    @10
    @14
    @29
    wi
    vz
    cn0
    @0
    cn0
    wcel
    #
    @10
    wa
    #
    @14
    @29
    @31
    @14
    wa
    #
    @28
    c2
    @0
    cmul
    co
    #
    @16
    clt
    wbr
    #
    @26
    wi
    #
    vn
    cn0
    wral
    #
    vs
    @33
    cn0
    @30
    @33
    cn0
    wcel
    @10
    @14
    @30
    c2
    @0
    c2
    cn0
    wcel
    @30
    2nn0
    a1i
    @30
    id
    nn0mulcld
    ad2antrr
    @15
    @33
    wceq
    #
    @28
    @36
    wb
    @32
    @37
    @27
    @35
    vn
    cn0
    @37
    @17
    @34
    @26
    @15
    @33
    @16
    clt
    breq1
    imbi1d
    ralbidv
    adantl
    @32
    @35
    vn
    cn0
    @32
    @16
    cn0
    wcel
    #
    wa
    #
    @34
    @26
    @39
    @34
    wa
    #
    @25
    cR
    vl
    @18
    @4
    cmpt
    #
    cgsu
    co
    #
    @4
    @40
    @24
    @41
    cR
    cgsu
    @40
    vl
    @18
    @23
    @4
    @19
    @0
    cle
    wbr
    #
    @40
    @19
    @18
    wcel
    #
    wa
    #
    @23
    @4
    wceq
    @43
    @45
    wa
    #
    @23
    @20
    @4
    c.as
    co
    #
    @4
    @46
    @22
    @4
    @20
    c.as
    @46
    @0
    @21
    clt
    wbr
    #
    @22
    @4
    wceq
    #
    @45
    @43
    @48
    @32
    @38
    @34
    @44
    @43
    @48
    wi
    #
    @30
    @38
    @34
    @44
    @50
    wi
    wi
    #
    wi
    @10
    @14
    @30
    @38
    @51
    @30
    @38
    wa
    #
    @44
    @34
    @50
    @52
    @44
    @34
    @50
    wi
    @52
    @44
    wa
    #
    @34
    @33
    @19
    cmin
    co
    #
    @21
    clt
    wbr
    #
    @50
    @53
    @33
    @16
    @19
    @30
    @33
    cr
    wcel
    #
    @38
    @44
    @30
    c2
    @0
    c2
    cr
    wcel
    @30
    2re
    a1i
    @0
    nn0re
    #
    remulcld
    #
    ad2antrr
    #
    @52
    @16
    cr
    wcel
    #
    @44
    @38
    @60
    @30
    @16
    nn0re
    adantl
    #
    adantr
    @44
    @19
    cr
    wcel
    #
    @52
    @44
    @19
    cn0
    wcel
    #
    @62
    @19
    @16
    elfznn0
    #
    @19
    nn0re
    #
    syl
    #
    adantl
    #
    ltsub1d
    @53
    @55
    @50
    @53
    @55
    wa
    @43
    @33
    @0
    cmin
    co
    #
    @54
    cle
    wbr
    #
    @48
    @53
    @43
    @69
    wb
    @55
    @53
    @19
    @0
    @33
    @67
    @30
    @0
    cr
    wcel
    #
    @38
    @44
    @57
    ad2antrr
    @59
    lesub2d
    adantr
    @53
    @55
    @69
    @48
    wi
    @53
    @69
    @55
    @48
    @53
    @69
    @55
    wa
    #
    @68
    @21
    clt
    wbr
    #
    @48
    @53
    @68
    cr
    wcel
    #
    @54
    cr
    wcel
    #
    @21
    cr
    wcel
    #
    @71
    @72
    wi
    @30
    @73
    @38
    @44
    @30
    @33
    @0
    @58
    @57
    resubcld
    ad2antrr
    @52
    @56
    @62
    @74
    @44
    @30
    @56
    @38
    @58
    adantr
    @66
    @33
    @19
    resubcl
    syl2an
    @52
    @60
    @62
    @75
    @44
    @61
    @66
    @16
    @19
    resubcl
    syl2an
    @68
    @54
    @21
    lelttr
    syl3anc
    @53
    @68
    @0
    @21
    clt
    @30
    @68
    @0
    wceq
    #
    @38
    @44
    @30
    @0
    cc
    wcel
    @76
    @0
    nn0cn
    @0
    2txmxeqx
    syl
    ad2antrr
    breq1d
    sylibd
    expcomd
    imp
    sylbid
    ex
    sylbid
    ex
    com23
    ex
    ad2antrr
    imp41
    impcom
    @45
    @48
    @49
    wi
    #
    @43
    @40
    @44
    @77
    @10
    @44
    @77
    wi
    @30
    @14
    @38
    @34
    @44
    @10
    @77
    @44
    @21
    @18
    wcel
    @21
    cn0
    wcel
    #
    @10
    @77
    wi
    @19
    @16
    fznn0sub2
    @21
    @16
    elfznn0
    @78
    @10
    @77
    @78
    @10
    wa
    @48
    @21
    cA
    cfv
    #
    @4
    wceq
    #
    @49
    wa
    #
    @49
    @9
    @48
    @81
    wi
    vx
    @21
    cn0
    @1
    @21
    wceq
    #
    @2
    @48
    @8
    @81
    @1
    @21
    @0
    clt
    breq2
    @82
    @5
    @80
    @7
    @49
    @82
    @3
    @79
    @4
    @1
    @21
    cA
    fveq2
    eqeq1d
    @82
    @6
    @22
    @4
    @1
    @21
    cC
    fveq2
    eqeq1d
    anbi12d
    imbi12d
    rspcva
    @80
    @49
    simpr
    syl6
    ex
    3syl
    com12
    ad4antlr
    imp
    adantl
    mpd
    oveq2d
    @46
    @11
    @20
    cR
    cbs
    cfv
    #
    wcel
    #
    @47
    @4
    wceq
    @45
    @11
    @43
    @39
    @11
    @34
    @44
    @11
    @12
    @13
    @31
    @38
    simplr1
    ad2antrr
    #
    adantl
    @46
    @12
    @63
    wa
    #
    @84
    @45
    @86
    @43
    @40
    @12
    @44
    @63
    @39
    @12
    @34
    @11
    @12
    @13
    @31
    @38
    simplr2
    adantr
    @64
    anim12i
    adantl
    cA
    cB
    cP
    cR
    cK
    @83
    @19
    ply1mulgsum.a
    ply1mulgsum.b
    ply1mulgsum.p
    @83
    eqid
    #
    coe1fvalcl
    syl
    @83
    cR
    c.as
    @20
    @4
    @87
    ply1mulgsum.rm
    @4
    eqid
    #
    ringrz
    syl2anc
    eqtrd
    @43
    wn
    #
    @45
    wa
    #
    @23
    @4
    @22
    c.as
    co
    #
    @4
    @90
    @20
    @4
    @22
    c.as
    @45
    @89
    @20
    @4
    wceq
    #
    @45
    @89
    @0
    @19
    clt
    wbr
    #
    @92
    @40
    @44
    @89
    @93
    wb
    #
    @30
    @44
    @94
    wi
    @10
    @14
    @38
    @34
    @63
    @30
    @94
    @44
    @30
    @63
    @94
    @30
    @63
    wa
    @93
    @89
    @30
    @70
    @62
    @93
    @89
    wb
    @63
    @57
    @65
    @0
    @19
    ltnle
    syl2an
    bicomd
    expcom
    @64
    syl11
    ad4antr
    imp
    @40
    @44
    @93
    @92
    wi
    #
    @10
    @44
    @95
    wi
    @30
    @14
    @38
    @34
    @63
    @10
    @95
    @44
    @63
    @10
    @95
    @63
    @10
    wa
    @93
    @92
    @19
    cC
    cfv
    #
    @4
    wceq
    #
    wa
    #
    @92
    @9
    @93
    @98
    wi
    vx
    @19
    cn0
    vx
    vl
    weq
    #
    @2
    @93
    @8
    @98
    @1
    @19
    @0
    clt
    breq2
    @99
    @5
    @92
    @7
    @97
    @99
    @3
    @20
    @4
    @1
    @19
    cA
    fveq2
    eqeq1d
    @99
    @6
    @96
    @4
    @1
    @19
    cC
    fveq2
    eqeq1d
    anbi12d
    imbi12d
    rspcva
    @92
    @97
    simpl
    syl6
    ex
    @64
    syl11
    ad4antlr
    imp
    sylbid
    impcom
    oveq1d
    @90
    @11
    @22
    @83
    wcel
    #
    @91
    @4
    wceq
    @45
    @11
    @89
    @85
    adantl
    @90
    @13
    @78
    wa
    #
    @100
    @45
    @101
    @89
    @40
    @13
    @44
    @78
    @39
    @13
    @34
    @11
    @12
    @13
    @31
    @38
    simplr3
    adantr
    @19
    cc0
    @16
    fznn0sub
    anim12i
    adantl
    cC
    cB
    cP
    cR
    cL
    @83
    @21
    ply1mulgsum.c
    ply1mulgsum.b
    ply1mulgsum.p
    @87
    coe1fvalcl
    syl
    @83
    cR
    c.as
    @22
    @4
    @87
    ply1mulgsum.rm
    @88
    ringlz
    syl2anc
    eqtrd
    pm2.61ian
    mpteq2dva
    oveq2d
    @40
    cR
    cmnd
    wcel
    #
    @18
    cvv
    wcel
    #
    wa
    #
    @42
    @4
    wceq
    @14
    @104
    @31
    @38
    @34
    @14
    @102
    @103
    @11
    @12
    @102
    @13
    cR
    ringmnd
    3ad2ant1
    cc0
    @16
    cfz
    ovex
    jctir
    ad3antlr
    @18
    vl
    cR
    cvv
    @4
    @88
    gsumz
    syl
    eqtrd
    ex
    ralrimiva
    rspcedvd
    ex
    rexlimiva
    mpcom
end
