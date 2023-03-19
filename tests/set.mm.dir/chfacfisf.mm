include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cv.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cn0.mm"
include "wceq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cbs.mm"
include "cgrp.mm"
include "pmatring.mm"
include "3adant3.mm"
include "ringgrp.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "ring0cl.mm"
include "mat2pmatbas.mm"
include "3simpa.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "cuz.mm"
include "nnnn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "ffvelrnd.mm"
include "anim12i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "grpsubcl.mm"
include "ad2antrr.mm"
include "wn.mm"
include "eluzfz2.mm"
include "anim1i.mm"
include "ancomd.mm"
include "m2pmfzmap.mm"
include "syl2anc.mm"
include "ad4antr.mm"
include "wi.mm"
include "cle.mm"
include "cr.mm"
include "nn0re.mm"
include "peano2nn.mm"
include "nnred.mm"
include "lenltd.mm"
include "wne.mm"
include "nesym.mm"
include "wb.mm"
include "ltlen.mm"
include "syl2anr.mm"
include "biimprd.mm"
include "expcomd.mm"
include "syl5bir.mm"
include "com23.mm"
include "sylbird.mm"
include "impd.mm"
include "ex.mm"
include "ad2antrl.mm"
include "imp.mm"
include "ad4antlr.mm"
include "id.mm"
include "necon3bi.mm"
include "anim2i.mm"
include "elnnne0.mm"
include "nnm1nn0.mm"
include "adantll.mm"
include "simprbda.mm"
include "1red.mm"
include "nnre.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "exp31.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "sylanbrc.mm"
include "simprr.mm"
include "simplr.mm"
include "cz.mm"
include "nn0z.mm"
include "nnz.mm"
include "zleltp1.mm"
include "biimpar.mm"
include "imp31.mm"
include "syl12anc.mm"
include "adantlr.mm"
include "syld.mm"
include "impl.mm"
include "ifclda.mm"
include "fmptd.mm"

theorem chfacfisf
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let vn: setvar n
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  assume chfacfisf.a: |- A = ( N Mat R )
  assume chfacfisf.b: |- B = ( Base ` A )
  assume chfacfisf.p: |- P = ( Poly1 ` R )
  assume chfacfisf.y: |- Y = ( N Mat P )
  assume chfacfisf.r: |- .X. = ( .r ` Y )
  assume chfacfisf.s: |- .- = ( -g ` Y )
  assume chfacfisf.0: |- .0. = ( 0g ` Y )
  assume chfacfisf.t: |- T = ( N matToPolyMat R )
  assume chfacfisf.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> G : NN0 --> ( Base ` Y ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
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
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    c.0
    cM
    cT
    cfv
    #
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
    @11
    @4
    c1
    caddc
    co
    #
    wceq
    #
    @4
    @6
    cfv
    cT
    cfv
    #
    @18
    @11
    clt
    wbr
    #
    c.0
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
    @13
    @11
    @6
    cfv
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
    cY
    cbs
    cfv
    #
    cG
    @10
    @11
    cn0
    wcel
    #
    wa
    #
    @12
    @17
    @29
    @30
    @10
    @17
    @30
    wcel
    #
    @31
    @12
    @10
    cY
    cgrp
    wcel
    #
    c.0
    @30
    wcel
    #
    @16
    @30
    wcel
    #
    @33
    @3
    @34
    @9
    @3
    cY
    crg
    wcel
    #
    @34
    @0
    @1
    @37
    @2
    cY
    cP
    cR
    cN
    chfacfisf.p
    chfacfisf.y
    pmatring
    #
    3adant3
    #
    cY
    ringgrp
    #
    syl
    adantr
    @3
    @35
    @9
    @3
    @37
    @35
    @39
    @30
    cY
    c.0
    @30
    eqid
    #
    chfacfisf.0
    ring0cl
    syl
    adantr
    #
    @10
    @37
    @13
    @30
    wcel
    #
    @15
    @30
    wcel
    #
    @36
    @3
    @37
    @9
    @39
    adantr
    #
    @3
    @43
    @9
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
    adantr
    #
    @10
    @0
    @1
    @14
    cB
    wcel
    #
    w3a
    #
    @44
    @10
    @0
    @1
    wa
    #
    @47
    wa
    @48
    @3
    @49
    @9
    @47
    @0
    @1
    @2
    3simpa
    #
    @9
    @7
    cB
    cc0
    @6
    @8
    @7
    cB
    @6
    wf
    #
    @5
    @6
    cB
    @7
    elmapi
    adantl
    #
    @5
    cc0
    @7
    wcel
    #
    @8
    @5
    @4
    cc0
    cuz
    cfv
    #
    wcel
    #
    @53
    @5
    @4
    cn0
    @54
    @4
    nnnn0
    #
    nn0uz
    syl6eleq
    #
    cc0
    @4
    eluzfz1
    syl
    adantr
    ffvelrnd
    anim12i
    @0
    @1
    @47
    df-3an
    sylibr
    cA
    cB
    cY
    cP
    cR
    cT
    @14
    cN
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    mat2pmatbas
    syl
    @30
    cY
    c.xp
    @13
    @15
    @41
    chfacfisf.r
    ringcl
    syl3anc
    @30
    cY
    c.mi
    c.0
    @16
    @41
    chfacfisf.s
    grpsubcl
    syl3anc
    ad2antrr
    @32
    @12
    wn
    #
    wa
    #
    @19
    @20
    @28
    @30
    @32
    @20
    @30
    wcel
    #
    @58
    @19
    @10
    @60
    @31
    @10
    @0
    @1
    @4
    cn0
    wcel
    #
    w3a
    #
    @8
    @4
    @7
    wcel
    #
    wa
    #
    @60
    @10
    @49
    @61
    wa
    @62
    @3
    @49
    @9
    @61
    @50
    @5
    @61
    @8
    @56
    adantr
    #
    anim12i
    @0
    @1
    @61
    df-3an
    sylibr
    #
    @9
    @64
    @3
    @9
    @63
    @8
    @5
    @63
    @8
    @5
    @55
    @63
    @57
    cc0
    @4
    eluzfz2
    syl
    anim1i
    ancomd
    adantl
    cA
    cB
    cP
    cR
    @4
    cT
    @4
    cN
    cY
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.t
    m2pmfzmap
    syl2anc
    adantr
    ad2antrr
    @59
    @19
    wn
    #
    wa
    @21
    c.0
    @27
    @30
    @10
    @35
    @31
    @58
    @67
    @21
    @42
    ad4antr
    @59
    @67
    @21
    wn
    #
    @27
    @30
    wcel
    #
    @59
    @67
    @68
    wa
    #
    @11
    @18
    clt
    wbr
    #
    @69
    @32
    @70
    @71
    wi
    #
    @58
    @10
    @31
    @72
    @5
    @31
    @72
    wi
    @3
    @8
    @5
    @31
    @72
    @5
    @31
    wa
    #
    @67
    @68
    @71
    @73
    @68
    @67
    @71
    @73
    @68
    @11
    @18
    cle
    wbr
    #
    @67
    @71
    wi
    @73
    @11
    @18
    @31
    @11
    cr
    wcel
    #
    @5
    @11
    nn0re
    #
    adantl
    #
    @5
    @18
    cr
    wcel
    #
    @31
    @5
    @18
    @4
    peano2nn
    nnred
    #
    adantr
    lenltd
    @73
    @67
    @74
    @71
    @67
    @18
    @11
    wne
    #
    @73
    @74
    @71
    wi
    @18
    @11
    nesym
    @73
    @74
    @80
    @71
    @73
    @71
    @74
    @80
    wa
    #
    @31
    @75
    @78
    @71
    @81
    wb
    @5
    @76
    @79
    @11
    @18
    ltlen
    syl2anr
    #
    biimprd
    expcomd
    syl5bir
    com23
    sylbird
    com23
    impd
    ex
    ad2antrl
    imp
    adantr
    @59
    @71
    @69
    @59
    @71
    wa
    #
    @34
    @24
    @30
    wcel
    #
    @26
    @30
    wcel
    #
    @69
    @3
    @34
    @9
    @31
    @58
    @71
    @0
    @1
    @34
    @2
    @49
    @37
    @34
    @38
    @40
    syl
    3adant3
    ad4antr
    @83
    @0
    @1
    @23
    cB
    wcel
    #
    w3a
    #
    @84
    @83
    @49
    @86
    @87
    @3
    @49
    @9
    @31
    @58
    @71
    @50
    ad4antr
    @83
    @7
    cB
    @22
    @6
    @9
    @51
    @3
    @31
    @58
    @71
    @52
    ad4antlr
    @83
    @22
    cn0
    wcel
    #
    @61
    @22
    @4
    cle
    wbr
    #
    @22
    @7
    wcel
    @59
    @88
    @71
    @31
    @58
    @88
    @10
    @31
    @58
    wa
    #
    @11
    cn
    wcel
    #
    @88
    @90
    @31
    @11
    cc0
    wne
    #
    wa
    @91
    @58
    @92
    @31
    @12
    @11
    cc0
    @12
    id
    necon3bi
    anim2i
    @11
    elnnne0
    sylibr
    @11
    nnm1nn0
    syl
    adantll
    adantr
    @9
    @61
    @3
    @31
    @58
    @71
    @65
    ad4antlr
    @59
    @71
    @89
    @32
    @71
    @89
    wi
    #
    @58
    @10
    @31
    @93
    @5
    @31
    @93
    wi
    @3
    @8
    @5
    @31
    @71
    @89
    @73
    @71
    wa
    #
    @89
    @74
    @73
    @71
    @74
    @80
    @82
    simprbda
    @94
    @11
    c1
    @4
    @73
    @75
    @71
    @77
    adantr
    @94
    1red
    @5
    @4
    cr
    wcel
    @31
    @71
    @4
    nnre
    ad2antrr
    lesubaddd
    mpbird
    exp31
    ad2antrl
    imp
    adantr
    imp
    @22
    @4
    elfz2nn0
    syl3anbrc
    ffvelrnd
    @0
    @1
    @86
    df-3an
    sylanbrc
    cA
    cB
    cY
    cP
    cR
    cT
    @23
    cN
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    mat2pmatbas
    syl
    @32
    @71
    @85
    @58
    @32
    @71
    wa
    #
    @37
    @43
    @25
    @30
    wcel
    #
    @85
    @10
    @37
    @31
    @71
    @45
    ad2antrr
    @10
    @43
    @31
    @71
    @46
    ad2antrr
    @95
    @62
    @8
    @11
    @7
    wcel
    #
    @96
    @10
    @62
    @31
    @71
    @66
    ad2antrr
    @10
    @8
    @31
    @71
    @3
    @5
    @8
    simprr
    ad2antrr
    @10
    @31
    @71
    @97
    @5
    @31
    @71
    @97
    wi
    wi
    @3
    @8
    @5
    @31
    @71
    @97
    @94
    @31
    @61
    @11
    @4
    cle
    wbr
    #
    @97
    @5
    @31
    @71
    simplr
    @5
    @61
    @31
    @71
    @56
    ad2antrr
    @73
    @98
    @71
    @31
    @11
    cz
    wcel
    @4
    cz
    wcel
    @98
    @71
    wb
    @5
    @11
    nn0z
    @4
    nnz
    @11
    @4
    zleltp1
    syl2anr
    biimpar
    @11
    @4
    elfz2nn0
    syl3anbrc
    exp31
    ad2antrl
    imp31
    cA
    cB
    cP
    cR
    @4
    cT
    @11
    cN
    cY
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.t
    m2pmfzmap
    syl12anc
    @30
    cY
    c.xp
    @13
    @25
    @41
    chfacfisf.r
    ringcl
    syl3anc
    adantlr
    @30
    cY
    c.mi
    @24
    @26
    @41
    chfacfisf.s
    grpsubcl
    syl3anc
    ex
    syld
    impl
    ifclda
    ifclda
    ifclda
    chfacfisf.g
    fmptd
end
