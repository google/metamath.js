include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "chash.mm"
include "cq1p.mm"
include "co.mm"
include "cun.mm"
include "cle.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wo.mm"
include "cmulr.mm"
include "cof.mm"
include "cpws.mm"
include "cdsr.mm"
include "wbr.mm"
include "wfn.mm"
include "wb.mm"
include "cbs.mm"
include "cidom.mm"
include "cvv.mm"
include "eqid.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "crh.mm"
include "wf.mm"
include "ccrg.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "syl.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "pwselbas.mm"
include "ffnd.mm"
include "fniniseg.mm"
include "mpbid.mm"
include "simprd.mm"
include "cnzr.mm"
include "simprbi.mm"
include "domnnzr.mm"
include "simpld.mm"
include "facth1.mm"
include "mpbird.mm"
include "crg.mm"
include "cuc1p.mm"
include "nzrring.mm"
include "cmn1.mm"
include "c1.mm"
include "ply1remlem.mm"
include "simp1d.mm"
include "mon1puc1p.mm"
include "syl2anc.mm"
include "dvdsq1p.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "q1pcl.mm"
include "mon1pcl.mm"
include "rhmmul.mm"
include "pwsmulrval.mm"
include "3eqtrd.mm"
include "fveq1d.mm"
include "adantr.mm"
include "simpr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "ffvelrnda.mm"
include "domneq0.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "andi.mm"
include "syl6bb.mm"
include "elun.mm"
include "simp3d.mm"
include "eleq2d.mm"
include "bitr3d.mm"
include "orbi12d.mm"
include "syl5bb.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "caddc.mm"
include "cfn.mm"
include "cn0.mm"
include "cnvex.mm"
include "imaex.mm"
include "wi.mm"
include "wral.mm"
include "fta1glem1.mm"
include "fveq2.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "breqtrd.mm"
include "hashbnd.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "hashcl.mm"
include "nn0red.mm"
include "cr.mm"
include "peano2re.mm"
include "peano2nn0.mm"
include "eqeltrd.mm"
include "hashun2.mm"
include "hashsng.mm"
include "oveq2d.mm"
include "1red.mm"
include "leadd1dd.mm"
include "breqtrrd.mm"
include "letrd.mm"
include "eqbrtrd.mm"

theorem fta1glem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vd: setvar d
  let vf: setvar f
  let vx: setvar x
  assume fta1g.p: |- P = ( Poly1 ` R )
  assume fta1g.b: |- B = ( Base ` P )
  assume fta1g.d: |- D = ( deg1 ` R )
  assume fta1g.o: |- O = ( eval1 ` R )
  assume fta1g.w: |- W = ( 0g ` R )
  assume fta1g.z: |- .0. = ( 0g ` P )
  assume fta1g.1: |- ( ph -> R e. IDomn )
  assume fta1g.2: |- ( ph -> F e. B )
  assume fta1glem.k: |- K = ( Base ` R )
  assume fta1glem.x: |- X = ( var1 ` R )
  assume fta1glem.m: |- .- = ( -g ` P )
  assume fta1glem.a: |- A = ( algSc ` P )
  assume fta1glem.g: |- G = ( X .- ( A ` T ) )
  assume fta1glem.3: |- ( ph -> N e. NN0 )
  assume fta1glem.4: |- ( ph -> ( D ` F ) = ( N + 1 ) )
  assume fta1glem.5: |- ( ph -> T e. ( `' ( O ` F ) " { W } ) )
  assume fta1glem.6: |- ( ph -> A. g e. B ( ( D ` g ) = N -> ( # ` ( `' ( O ` g ) " { W } ) ) <_ ( D ` g ) ) )

  disjoint B g
  disjoint D g
  disjoint F g
  disjoint N g
  disjoint O g
  disjoint G g
  disjoint P g
  disjoint R g
  disjoint W g
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint B d
  disjoint f g
  disjoint f x
  disjoint B f
  disjoint g x
  disjoint B x
  disjoint D d
  disjoint D f
  disjoint D x
  disjoint F f
  disjoint F x
  disjoint O d
  disjoint O f
  disjoint O x
  disjoint G x
  disjoint ph x
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint W d
  disjoint W f
  disjoint W x
  disjoint T x
  assert |- ( ph -> ( # ` ( `' ( O ` F ) " { W } ) ) <_ ( D ` F ) )

  proof
    wph
    cF
    cO
    cfv
    #
    ccnv
    cW
    csn
    #
    cima
    #
    chash
    cfv
    cF
    cG
    cR
    cq1p
    cfv
    #
    co
    #
    cO
    cfv
    #
    ccnv
    #
    @1
    cima
    #
    cT
    csn
    #
    cun
    #
    chash
    cfv
    #
    cF
    cD
    cfv
    #
    cle
    wph
    @2
    @9
    chash
    wph
    vx
    @2
    @9
    wph
    vx
    cv
    #
    cK
    wcel
    #
    @12
    @0
    cfv
    #
    cW
    wceq
    #
    wa
    #
    @13
    @12
    @5
    cfv
    #
    cW
    wceq
    #
    wa
    #
    @13
    @12
    cG
    cO
    cfv
    #
    cfv
    #
    cW
    wceq
    #
    wa
    #
    wo
    #
    @12
    @2
    wcel
    #
    @12
    @9
    wcel
    #
    wph
    @16
    @13
    @18
    @22
    wo
    #
    wa
    @24
    wph
    @13
    @15
    @27
    wph
    @13
    wa
    #
    @15
    @17
    @21
    cR
    cmulr
    cfv
    #
    co
    #
    cW
    wceq
    #
    @27
    @28
    @14
    @30
    cW
    @28
    @14
    @12
    @5
    @20
    @29
    cof
    co
    #
    cfv
    #
    @30
    wph
    @14
    @33
    wceq
    @13
    wph
    @12
    @0
    @32
    wph
    @0
    @4
    cG
    cP
    cmulr
    cfv
    #
    co
    #
    cO
    cfv
    #
    @5
    @20
    cR
    cK
    cpws
    co
    #
    cmulr
    cfv
    #
    co
    #
    @32
    wph
    cF
    @35
    cO
    wph
    cG
    cF
    cP
    cdsr
    cfv
    #
    wbr
    #
    cF
    @35
    wceq
    #
    wph
    @41
    cT
    @0
    cfv
    cW
    wceq
    #
    wph
    cT
    cK
    wcel
    #
    @43
    wph
    cT
    @2
    wcel
    #
    @44
    @43
    wa
    #
    fta1glem.5
    wph
    @0
    cK
    wfn
    #
    @45
    @46
    wb
    wph
    cK
    cK
    @0
    wph
    cK
    cR
    cK
    @37
    cbs
    cfv
    #
    cidom
    @0
    @37
    cvv
    @37
    eqid
    #
    fta1glem.k
    @48
    eqid
    #
    fta1g.1
    cK
    cvv
    wcel
    #
    wph
    cK
    cR
    cbs
    cfv
    cvv
    fta1glem.k
    cR
    cbs
    fvex
    eqeltri
    #
    a1i
    #
    wph
    cB
    @48
    cF
    cO
    wph
    cO
    cP
    @37
    crh
    co
    wcel
    #
    cB
    @48
    cO
    wf
    wph
    cR
    ccrg
    wcel
    #
    @54
    wph
    cR
    cidom
    wcel
    #
    @55
    fta1g.1
    @56
    @55
    cR
    cdomn
    wcel
    #
    cR
    isidom
    #
    simplbi
    syl
    #
    cK
    cP
    cR
    @37
    cO
    fta1g.o
    fta1g.p
    @49
    fta1glem.k
    evl1rhm
    syl
    #
    cB
    @48
    cP
    @37
    cO
    fta1g.b
    @50
    rhmf
    syl
    #
    fta1g.2
    ffvelrnd
    pwselbas
    ffnd
    #
    cK
    cW
    cT
    @0
    fniniseg
    syl
    mpbid
    #
    simprd
    wph
    cA
    cB
    @40
    cP
    cR
    cF
    cG
    cK
    c.mi
    cT
    cO
    cX
    cW
    fta1g.p
    fta1g.b
    fta1glem.k
    fta1glem.x
    fta1glem.m
    fta1glem.a
    fta1glem.g
    fta1g.o
    wph
    @56
    cR
    cnzr
    wcel
    #
    fta1g.1
    @56
    @57
    @64
    @56
    @55
    @57
    @58
    simprbi
    #
    cR
    domnnzr
    syl
    syl
    #
    @59
    wph
    @44
    @43
    @63
    simpld
    #
    fta1g.2
    fta1g.w
    @40
    eqid
    #
    facth1
    mpbird
    wph
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cR
    cuc1p
    cfv
    #
    wcel
    #
    @41
    @42
    wb
    wph
    @64
    @69
    @66
    cR
    nzrring
    syl
    #
    fta1g.2
    wph
    @69
    cG
    cR
    cmn1
    cfv
    #
    wcel
    #
    @72
    @73
    wph
    @75
    cG
    cD
    cfv
    c1
    wceq
    #
    @20
    ccnv
    @1
    cima
    #
    @8
    wceq
    #
    wph
    cA
    cB
    cD
    cP
    cR
    @74
    cG
    cK
    c.mi
    cT
    cO
    cX
    cW
    fta1g.p
    fta1g.b
    fta1glem.k
    fta1glem.x
    fta1glem.m
    fta1glem.a
    fta1glem.g
    fta1g.o
    @66
    @59
    @67
    @74
    eqid
    #
    fta1g.d
    fta1g.w
    ply1remlem
    #
    simp1d
    #
    @71
    cR
    @74
    cG
    @71
    eqid
    #
    @79
    mon1puc1p
    syl2anc
    #
    cB
    @71
    @40
    cP
    @3
    cR
    @34
    cF
    cG
    fta1g.p
    @68
    fta1g.b
    @82
    @34
    eqid
    #
    @3
    eqid
    #
    dvdsq1p
    syl3anc
    mpbid
    fveq2d
    wph
    @54
    @4
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    @36
    @39
    wceq
    @60
    wph
    @69
    @70
    @72
    @86
    @73
    fta1g.2
    @83
    cB
    @71
    cP
    @3
    cR
    cF
    cG
    @85
    fta1g.p
    fta1g.b
    @82
    q1pcl
    syl3anc
    #
    wph
    @75
    @87
    @81
    cB
    cP
    cR
    cG
    @74
    fta1g.p
    fta1g.b
    @79
    mon1pcl
    syl
    #
    @4
    cG
    cP
    @37
    @34
    @38
    cO
    cB
    fta1g.b
    @84
    @38
    eqid
    #
    rhmmul
    syl3anc
    wph
    @48
    cR
    @38
    @29
    @5
    @20
    cK
    cidom
    cvv
    @37
    @49
    @50
    fta1g.1
    @53
    wph
    cB
    @48
    @4
    cO
    @61
    @88
    ffvelrnd
    #
    wph
    cB
    @48
    cG
    cO
    @61
    @89
    ffvelrnd
    #
    @29
    eqid
    #
    @90
    pwsmulrval
    3eqtrd
    fveq1d
    adantr
    @28
    @5
    cK
    wfn
    #
    @20
    cK
    wfn
    #
    @51
    @13
    @33
    @30
    wceq
    wph
    @94
    @13
    wph
    cK
    cK
    @5
    wph
    cK
    cR
    cK
    @48
    cidom
    @5
    @37
    cvv
    @49
    fta1glem.k
    @50
    fta1g.1
    @53
    @91
    pwselbas
    #
    ffnd
    #
    adantr
    wph
    @95
    @13
    wph
    cK
    cK
    @20
    wph
    cK
    cR
    cK
    @48
    cidom
    @20
    @37
    cvv
    @49
    fta1glem.k
    @50
    fta1g.1
    @53
    @92
    pwselbas
    #
    ffnd
    #
    adantr
    @51
    @28
    @52
    a1i
    wph
    @13
    simpr
    cK
    @29
    @5
    @20
    cvv
    @12
    fnfvof
    syl22anc
    eqtrd
    eqeq1d
    @28
    @57
    @17
    cK
    wcel
    @21
    cK
    wcel
    @31
    @27
    wb
    wph
    @57
    @13
    wph
    @56
    @57
    fta1g.1
    @65
    syl
    adantr
    wph
    cK
    cK
    @12
    @5
    @96
    ffvelrnda
    wph
    cK
    cK
    @12
    @20
    @98
    ffvelrnda
    cK
    cR
    @29
    @17
    @21
    cW
    fta1glem.k
    @93
    fta1g.w
    domneq0
    syl3anc
    bitrd
    pm5.32da
    @13
    @18
    @22
    andi
    syl6bb
    wph
    @47
    @25
    @16
    wb
    @62
    cK
    cW
    @12
    @0
    fniniseg
    syl
    @26
    @12
    @7
    wcel
    #
    @12
    @8
    wcel
    #
    wo
    wph
    @24
    @12
    @7
    @8
    elun
    wph
    @100
    @19
    @101
    @23
    wph
    @94
    @100
    @19
    wb
    @97
    cK
    cW
    @12
    @5
    fniniseg
    syl
    wph
    @12
    @77
    wcel
    #
    @101
    @23
    wph
    @77
    @8
    @12
    wph
    @75
    @76
    @78
    @80
    simp3d
    eleq2d
    wph
    @95
    @102
    @23
    wb
    @99
    cK
    cW
    @12
    @20
    fniniseg
    syl
    bitr3d
    orbi12d
    syl5bb
    3bitr4d
    eqrdv
    fveq2d
    wph
    @10
    @7
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @11
    wph
    @10
    wph
    @9
    cfn
    wcel
    #
    @10
    cn0
    wcel
    wph
    @7
    cfn
    wcel
    #
    @8
    cfn
    wcel
    #
    @105
    wph
    @7
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    @103
    cN
    cle
    wbr
    @106
    @108
    wph
    @6
    @1
    @5
    @4
    cO
    fvex
    cnvex
    imaex
    a1i
    fta1glem.3
    wph
    @103
    @4
    cD
    cfv
    #
    cN
    cle
    wph
    @86
    vg
    cv
    #
    cD
    cfv
    #
    cN
    wceq
    #
    @111
    cO
    cfv
    #
    ccnv
    #
    @1
    cima
    #
    chash
    cfv
    #
    @112
    cle
    wbr
    #
    wi
    #
    vg
    cB
    wral
    @110
    cN
    wceq
    #
    @103
    @110
    cle
    wbr
    #
    @88
    fta1glem.6
    wph
    cA
    cB
    cD
    cP
    cR
    cT
    cF
    cG
    cK
    c.mi
    cN
    cO
    cW
    cX
    c.0
    fta1g.p
    fta1g.b
    fta1g.d
    fta1g.o
    fta1g.w
    fta1g.z
    fta1g.1
    fta1g.2
    fta1glem.k
    fta1glem.x
    fta1glem.m
    fta1glem.a
    fta1glem.g
    fta1glem.3
    fta1glem.4
    fta1glem.5
    fta1glem1
    #
    @119
    @120
    @121
    wi
    vg
    @4
    cB
    @111
    @4
    wceq
    #
    @113
    @120
    @118
    @121
    @123
    @112
    @110
    cN
    @111
    @4
    cD
    fveq2
    #
    eqeq1d
    @123
    @117
    @103
    @112
    @110
    cle
    @123
    @116
    @7
    chash
    @123
    @115
    @6
    @1
    @123
    @114
    @5
    @111
    @4
    cO
    fveq2
    cnveqd
    imaeq1d
    fveq2d
    @124
    breq12d
    imbi12d
    rspcv
    syl3c
    @122
    breqtrd
    #
    @7
    cN
    cvv
    hashbnd
    syl3anc
    #
    cT
    snfi
    #
    @7
    @8
    unfi
    sylancl
    @9
    hashcl
    syl
    nn0red
    wph
    @103
    cr
    wcel
    @104
    cr
    wcel
    wph
    @103
    wph
    @106
    @103
    cn0
    wcel
    @126
    @7
    hashcl
    syl
    nn0red
    #
    @103
    peano2re
    syl
    wph
    @11
    wph
    @11
    cN
    c1
    caddc
    co
    #
    cn0
    fta1glem.4
    wph
    @109
    @129
    cn0
    wcel
    fta1glem.3
    cN
    peano2nn0
    syl
    eqeltrd
    nn0red
    wph
    @10
    @103
    @8
    chash
    cfv
    #
    caddc
    co
    #
    @104
    cle
    wph
    @106
    @107
    @10
    @131
    cle
    wbr
    @126
    @127
    @7
    @8
    hashun2
    sylancl
    wph
    @130
    c1
    @103
    caddc
    wph
    @45
    @130
    c1
    wceq
    fta1glem.5
    cT
    @2
    hashsng
    syl
    oveq2d
    breqtrd
    wph
    @104
    @129
    @11
    cle
    wph
    @103
    cN
    c1
    @128
    wph
    cN
    fta1glem.3
    nn0red
    wph
    1red
    @125
    leadd1dd
    fta1glem.4
    breqtrrd
    letrd
    eqbrtrd
end
