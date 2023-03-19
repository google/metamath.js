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
include "csubg.mm"
include "cpmatsubgpmat.mm"
include "3adant3.mm"
include "adantr.mm"
include "csubmnd.mm"
include "subgsubm.mm"
include "subm0cl.mm"
include "3syl.mm"
include "csubrg.mm"
include "cpmatsrgpmat.mm"
include "m2cpm.mm"
include "3simpa.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "cuz.mm"
include "nnnn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "anim12i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "subrgmcl.mm"
include "syl3anc.mm"
include "subgsubcl.mm"
include "ad2antrr.mm"
include "wn.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eluzfz2.mm"
include "ad2antrl.mm"
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
include "simp1d.mm"
include "simp2d.mm"
include "simplr.mm"
include "cz.mm"
include "nn0z.mm"
include "nnz.mm"
include "zleltp1.mm"
include "biimpar.mm"
include "imp31.mm"
include "adantlr.mm"
include "syld.mm"
include "impl.mm"
include "ifclda.mm"
include "fmptd.mm"

theorem chfacfisfcpmat
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
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
  assume chfacfisfcpmat.s: |- S = ( N ConstPolyMat R )

  disjoint S n
  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> G : NN0 --> S )

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
    #
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
    cS
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
    @31
    cS
    @10
    @17
    cS
    wcel
    #
    @32
    @12
    @10
    cS
    cY
    csubg
    cfv
    wcel
    #
    c.0
    cS
    wcel
    #
    @16
    cS
    wcel
    #
    @34
    @3
    @35
    @9
    @0
    @1
    @35
    @2
    cY
    cP
    cR
    cS
    cN
    chfacfisfcpmat.s
    chfacfisf.p
    chfacfisf.y
    cpmatsubgpmat
    3adant3
    #
    adantr
    @3
    @36
    @9
    @3
    @35
    cS
    cY
    csubmnd
    cfv
    wcel
    @36
    @38
    cS
    cY
    subgsubm
    cS
    cY
    c.0
    chfacfisf.0
    subm0cl
    3syl
    adantr
    #
    @10
    cS
    cY
    csubrg
    cfv
    wcel
    #
    @13
    cS
    wcel
    #
    @15
    cS
    wcel
    #
    @37
    @3
    @40
    @9
    @0
    @1
    @40
    @2
    cY
    cP
    cR
    cS
    cN
    chfacfisfcpmat.s
    chfacfisf.p
    chfacfisf.y
    cpmatsrgpmat
    3adant3
    adantr
    #
    @3
    @41
    @9
    cA
    cB
    cR
    cS
    cT
    cM
    cN
    chfacfisfcpmat.s
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    m2cpm
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
    @42
    @10
    @0
    @1
    wa
    #
    @45
    wa
    @46
    @3
    @47
    @9
    @45
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
    @51
    @5
    @4
    cn0
    @52
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
    @45
    df-3an
    sylibr
    cA
    cB
    cR
    cS
    cT
    @14
    cN
    chfacfisfcpmat.s
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    m2cpm
    syl
    cS
    cY
    c.xp
    @13
    @15
    chfacfisf.r
    subrgmcl
    syl3anc
    cS
    cY
    c.mi
    c.0
    @16
    chfacfisf.s
    subgsubcl
    syl3anc
    ad2antrr
    @33
    @12
    wn
    #
    wa
    #
    @19
    @21
    @30
    cS
    @33
    @21
    cS
    wcel
    #
    @56
    @19
    @10
    @58
    @32
    @10
    @0
    @1
    @20
    cB
    wcel
    @58
    @0
    @1
    @2
    @9
    simpl1
    @0
    @1
    @2
    @9
    simpl2
    @10
    @7
    cB
    @4
    @6
    @9
    @49
    @3
    @50
    adantl
    #
    @5
    @4
    @7
    wcel
    #
    @3
    @8
    @5
    @53
    @60
    @55
    cc0
    @4
    eluzfz2
    syl
    ad2antrl
    ffvelrnd
    cA
    cB
    cR
    cS
    cT
    @20
    cN
    chfacfisfcpmat.s
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    m2cpm
    syl3anc
    adantr
    ad2antrr
    @57
    @19
    wn
    #
    wa
    @22
    c.0
    @29
    cS
    @10
    @36
    @32
    @56
    @61
    @22
    @39
    ad4antr
    @57
    @61
    @22
    wn
    #
    @29
    cS
    wcel
    #
    @57
    @61
    @62
    wa
    #
    @11
    @18
    clt
    wbr
    #
    @63
    @33
    @64
    @65
    wi
    #
    @56
    @10
    @32
    @66
    @5
    @32
    @66
    wi
    @3
    @8
    @5
    @32
    @66
    @5
    @32
    wa
    #
    @61
    @62
    @65
    @67
    @62
    @61
    @65
    @67
    @62
    @11
    @18
    cle
    wbr
    #
    @61
    @65
    wi
    @67
    @11
    @18
    @32
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
    @32
    @5
    @18
    @4
    peano2nn
    nnred
    #
    adantr
    lenltd
    @67
    @61
    @68
    @65
    @61
    @18
    @11
    wne
    #
    @67
    @68
    @65
    wi
    @18
    @11
    nesym
    @67
    @68
    @74
    @65
    @67
    @65
    @68
    @74
    wa
    #
    @32
    @69
    @72
    @65
    @75
    wb
    @5
    @70
    @73
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
    @57
    @65
    @63
    @57
    @65
    wa
    #
    @35
    @25
    cS
    wcel
    #
    @28
    cS
    wcel
    #
    @63
    @3
    @35
    @9
    @32
    @56
    @65
    @38
    ad4antr
    @77
    @0
    @1
    @24
    cB
    wcel
    #
    w3a
    #
    @78
    @77
    @47
    @80
    @81
    @3
    @47
    @9
    @32
    @56
    @65
    @48
    ad4antr
    @77
    @7
    cB
    @23
    @6
    @9
    @49
    @3
    @32
    @56
    @65
    @50
    ad4antlr
    @77
    @23
    cn0
    wcel
    #
    @4
    cn0
    wcel
    #
    @23
    @4
    cle
    wbr
    #
    @23
    @7
    wcel
    @57
    @82
    @65
    @32
    @56
    @82
    @10
    @32
    @56
    wa
    #
    @11
    cn
    wcel
    #
    @82
    @85
    @32
    @11
    cc0
    wne
    #
    wa
    @86
    @56
    @87
    @32
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
    @83
    @3
    @32
    @56
    @65
    @5
    @83
    @8
    @54
    adantr
    #
    ad4antlr
    @57
    @65
    @84
    @33
    @65
    @84
    wi
    #
    @56
    @10
    @32
    @89
    @5
    @32
    @89
    wi
    @3
    @8
    @5
    @32
    @65
    @84
    @67
    @65
    wa
    #
    @84
    @68
    @67
    @65
    @68
    @74
    @76
    simprbda
    @90
    @11
    c1
    @4
    @67
    @69
    @65
    @71
    adantr
    @90
    1red
    @5
    @4
    cr
    wcel
    @32
    @65
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
    @23
    @4
    elfz2nn0
    syl3anbrc
    ffvelrnd
    @0
    @1
    @80
    df-3an
    sylanbrc
    cA
    cB
    cR
    cS
    cT
    @24
    cN
    chfacfisfcpmat.s
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    m2cpm
    syl
    @33
    @65
    @79
    @56
    @33
    @65
    wa
    #
    @40
    @41
    @27
    cS
    wcel
    #
    @79
    @10
    @40
    @32
    @65
    @43
    ad2antrr
    @10
    @41
    @32
    @65
    @44
    ad2antrr
    @91
    @0
    @1
    @26
    cB
    wcel
    @92
    @91
    @0
    @1
    @83
    @10
    @0
    @1
    @83
    w3a
    #
    @32
    @65
    @10
    @47
    @83
    wa
    @93
    @3
    @47
    @9
    @83
    @48
    @88
    anim12i
    @0
    @1
    @83
    df-3an
    sylibr
    ad2antrr
    #
    simp1d
    @91
    @0
    @1
    @83
    @94
    simp2d
    @91
    @7
    cB
    @11
    @6
    @10
    @49
    @32
    @65
    @59
    ad2antrr
    @10
    @32
    @65
    @11
    @7
    wcel
    #
    @5
    @32
    @65
    @95
    wi
    wi
    @3
    @8
    @5
    @32
    @65
    @95
    @90
    @32
    @83
    @11
    @4
    cle
    wbr
    #
    @95
    @5
    @32
    @65
    simplr
    @5
    @83
    @32
    @65
    @54
    ad2antrr
    @67
    @96
    @65
    @32
    @11
    cz
    wcel
    @4
    cz
    wcel
    @96
    @65
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
    ffvelrnd
    cA
    cB
    cR
    cS
    cT
    @26
    cN
    chfacfisfcpmat.s
    chfacfisf.t
    chfacfisf.a
    chfacfisf.b
    m2cpm
    syl3anc
    cS
    cY
    c.xp
    @13
    @27
    chfacfisf.r
    subrgmcl
    syl3anc
    adantlr
    cS
    cY
    c.mi
    @25
    @28
    chfacfisf.s
    subgsubcl
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
