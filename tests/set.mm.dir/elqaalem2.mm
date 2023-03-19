include "cc0.mm"
include "cdgr.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "cv.mm"
include "cmo.mm"
include "cmpt.mm"
include "cn0.mm"
include "cseq.mm"
include "wceq.mm"
include "elfznn0.mm"
include "cmul.mm"
include "fveq2i.mm"
include "nnmulcl.mm"
include "adantl.mm"
include "cz.mm"
include "elqaalem1.mm"
include "simpld.mm"
include "adantlr.mm"
include "sylan2.mm"
include "cuz.mm"
include "cq.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "eldifi.mm"
include "dgrcl.mm"
include "3syl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "adantr.mm"
include "nnz.mm"
include "ad2antrl.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "ad2antll.mm"
include "nnrpd.mm"
include "cr.mm"
include "crp.mm"
include "nnre.mm"
include "modabs2.mm"
include "syl2anc.mm"
include "modmul12d.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "oveq12d.mm"
include "cvv.mm"
include "oveq12.mm"
include "oveq1d.mm"
include "ovmpt2a.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "syl.mm"
include "3eqtr4rd.mm"
include "fveq2.mm"
include "eqtr4d.mm"
include "seqhomo.mm"
include "syl5eq.mm"
include "0zd.mm"
include "seqf.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "vex.mm"
include "nn0mulcl.mm"
include "zmodcl.mm"
include "syl2anr.mm"
include "wf.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "nnzd.mm"
include "fmptd.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "c0ex.mm"
include "nn0cn.mm"
include "mul02d.mm"
include "0mod.mm"
include "sylan9eqr.mm"
include "mul01d.mm"
include "simpr.mm"
include "cdiv.mm"
include "c1.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "dividd.mm"
include "1z.mm"
include "syl6eqel.mm"
include "wb.mm"
include "nnred.mm"
include "mod0.mm"
include "mpbird.mm"
include "eqtrd.mm"
include "seqz.mm"
include "3eqtr3d.mm"

theorem elqaalem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  assume elqaa.1: |- ( ph -> A e. CC )
  assume elqaa.2: |- ( ph -> F e. ( ( Poly ` QQ ) \ { 0p } ) )
  assume elqaa.3: |- ( ph -> ( F ` A ) = 0 )
  assume elqaa.4: |- B = ( coeff ` F )
  assume elqaa.5: |- N = ( k e. NN0 |-> inf ( { n e. NN | ( ( B ` k ) x. n ) e. ZZ } , RR , < ) )
  assume elqaa.6: |- R = ( seq 0 ( x. , N ) ` ( deg ` F ) )
  assume elqaa.7: |- P = ( x e. _V , y e. _V |-> ( ( x x. y ) mod ( N ` K ) ) )

  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B n
  disjoint k ph
  disjoint K k
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint R k
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k m
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B m
  disjoint B z
  disjoint i j
  disjoint P i
  disjoint P j
  disjoint i k
  disjoint i m
  disjoint i z
  disjoint i ph
  disjoint j k
  disjoint j m
  disjoint j z
  disjoint j ph
  disjoint m ph
  disjoint ph z
  disjoint f i
  disjoint f j
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint F m
  disjoint F z
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint K i
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint R f
  disjoint R m
  disjoint R z
  assert |- ( ( ph /\ K e. ( 0 ... ( deg ` F ) ) ) -> ( R mod ( N ` K ) ) = 0 )

  proof
    wph
    cK
    cc0
    cF
    cdgr
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cR
    vk
    cn
    vk
    cv
    #
    cK
    cN
    cfv
    #
    cmo
    co
    #
    cmpt
    #
    cfv
    #
    @0
    cP
    vk
    cn0
    @4
    cN
    cfv
    #
    @5
    cmo
    co
    #
    cmpt
    #
    cc0
    cseq
    cfv
    #
    cR
    @5
    cmo
    co
    #
    cc0
    @2
    wph
    cK
    cn0
    wcel
    #
    @8
    @12
    wceq
    cK
    @0
    elfznn0
    #
    wph
    @14
    wa
    #
    @8
    @0
    cmul
    cN
    cc0
    cseq
    #
    cfv
    #
    @7
    cfv
    @12
    cR
    @18
    @7
    elqaa.6
    fveq2i
    @16
    vi
    vj
    cmul
    cP
    cn
    cN
    @11
    @7
    cc0
    @0
    vi
    cv
    #
    cn
    wcel
    #
    vj
    cv
    #
    cn
    wcel
    #
    wa
    #
    @19
    @21
    cmul
    co
    #
    cn
    wcel
    #
    @16
    @19
    @21
    nnmulcl
    #
    adantl
    #
    @19
    @1
    wcel
    #
    @16
    @19
    cn0
    wcel
    #
    @19
    cN
    cfv
    #
    cn
    wcel
    #
    @19
    @0
    elfznn0
    #
    wph
    @29
    @31
    @14
    wph
    @29
    wa
    @31
    @19
    cB
    cfv
    @30
    cmul
    co
    cz
    wcel
    wph
    cA
    cB
    cR
    vk
    vn
    cF
    @19
    cN
    elqaa.1
    elqaa.2
    elqaa.3
    elqaa.4
    elqaa.5
    elqaa.6
    elqaalem1
    simpld
    #
    adantlr
    #
    sylan2
    wph
    @0
    cc0
    cuz
    cfv
    #
    wcel
    @14
    wph
    @0
    cn0
    @35
    wph
    cF
    cq
    cply
    cfv
    #
    c0p
    csn
    #
    cdif
    wcel
    cF
    @36
    wcel
    @0
    cn0
    wcel
    #
    elqaa.2
    cF
    @36
    @37
    eldifi
    cq
    cF
    dgrcl
    3syl
    #
    nn0uz
    syl6eleq
    adantr
    @16
    @23
    wa
    #
    @19
    @5
    cmo
    co
    #
    @21
    @5
    cmo
    co
    #
    cmul
    co
    #
    @5
    cmo
    co
    #
    @24
    @5
    cmo
    co
    #
    @19
    @7
    cfv
    #
    @21
    @7
    cfv
    #
    cP
    co
    #
    @24
    @7
    cfv
    #
    @40
    @41
    @19
    @42
    @21
    @5
    @40
    @41
    @40
    @19
    @5
    @20
    @19
    cz
    wcel
    @16
    @22
    @19
    nnz
    ad2antrl
    #
    @16
    @5
    cn
    wcel
    #
    @23
    @16
    @51
    cK
    cB
    cfv
    @5
    cmul
    co
    cz
    wcel
    wph
    cA
    cB
    cR
    vk
    vn
    cF
    cK
    cN
    elqaa.1
    elqaa.2
    elqaa.3
    elqaa.4
    elqaa.5
    elqaa.6
    elqaalem1
    simpld
    #
    adantr
    #
    zmodcld
    nn0zd
    @50
    @40
    @42
    @40
    @21
    @5
    @22
    @21
    cz
    wcel
    @16
    @20
    @21
    nnz
    ad2antll
    #
    @53
    zmodcld
    nn0zd
    @54
    @40
    @5
    @53
    nnrpd
    #
    @40
    @19
    cr
    wcel
    #
    @5
    crp
    wcel
    #
    @41
    @5
    cmo
    co
    @41
    wceq
    @20
    @56
    @16
    @22
    @19
    nnre
    ad2antrl
    @55
    @19
    @5
    modabs2
    syl2anc
    @40
    @21
    cr
    wcel
    #
    @57
    @42
    @5
    cmo
    co
    @42
    wceq
    @22
    @58
    @16
    @20
    @21
    nnre
    ad2antll
    @55
    @21
    @5
    modabs2
    syl2anc
    modmul12d
    @40
    @48
    @41
    @42
    cP
    co
    #
    @44
    @40
    @46
    @41
    @47
    @42
    cP
    @20
    @46
    @41
    wceq
    @16
    @22
    vk
    @19
    @6
    @41
    cn
    @7
    @4
    @19
    @5
    cmo
    oveq1
    @7
    eqid
    #
    @19
    @5
    cmo
    ovex
    #
    fvmpt
    ad2antrl
    @22
    @47
    @42
    wceq
    @16
    @20
    vk
    @21
    @6
    @42
    cn
    @7
    @4
    @21
    @5
    cmo
    oveq1
    @60
    @21
    @5
    cmo
    ovex
    #
    fvmpt
    ad2antll
    oveq12d
    @41
    cvv
    wcel
    @42
    cvv
    wcel
    @59
    @44
    wceq
    @61
    @62
    vx
    vy
    @41
    @42
    cvv
    cvv
    vx
    cv
    #
    vy
    cv
    #
    cmul
    co
    #
    @5
    cmo
    co
    #
    @44
    cP
    @63
    @41
    wceq
    @64
    @42
    wceq
    wa
    @65
    @43
    @5
    cmo
    @63
    @41
    @64
    @42
    cmul
    oveq12
    oveq1d
    elqaa.7
    @43
    @5
    cmo
    ovex
    ovmpt2a
    mp2an
    syl6eq
    @40
    @25
    @49
    @45
    wceq
    @27
    vk
    @24
    @6
    @45
    cn
    @7
    @4
    @24
    @5
    cmo
    oveq1
    @60
    @24
    @5
    cmo
    ovex
    #
    fvmpt
    syl
    3eqtr4rd
    @28
    @16
    @29
    @30
    @7
    cfv
    #
    @19
    @11
    cfv
    #
    wceq
    @32
    @16
    @29
    wa
    #
    @68
    @30
    @5
    cmo
    co
    #
    @69
    @70
    @31
    @68
    @71
    wceq
    @34
    vk
    @30
    @6
    @71
    cn
    @7
    @4
    @30
    @5
    cmo
    oveq1
    @60
    @30
    @5
    cmo
    ovex
    #
    fvmpt
    syl
    @29
    @69
    @71
    wceq
    @16
    vk
    @19
    @10
    @71
    cn0
    @11
    @4
    @19
    wceq
    @9
    @30
    @5
    cmo
    @4
    @19
    cN
    fveq2
    oveq1d
    @11
    eqid
    #
    @72
    fvmpt
    adantl
    eqtr4d
    sylan2
    seqhomo
    syl5eq
    sylan2
    @2
    wph
    @14
    @8
    @13
    wceq
    #
    @15
    @16
    cR
    cn
    wcel
    #
    @74
    wph
    @75
    @14
    wph
    cR
    @18
    cn
    elqaa.6
    wph
    cn0
    cn
    @0
    @17
    wph
    vi
    vj
    cmul
    cn
    cN
    cc0
    cn0
    nn0uz
    wph
    0zd
    @33
    @23
    @25
    wph
    @26
    adantl
    seqf
    @39
    ffvelrnd
    syl5eqel
    adantr
    vk
    cR
    @6
    @13
    cn
    @7
    @4
    cR
    @5
    cmo
    oveq1
    @60
    cR
    @5
    cmo
    ovex
    fvmpt
    syl
    sylan2
    @3
    vi
    vj
    cP
    cn0
    @11
    cK
    cc0
    @0
    cn0
    cc0
    @3
    @29
    @21
    cn0
    wcel
    wa
    #
    wa
    @19
    @21
    cP
    co
    #
    @45
    cn0
    @19
    cvv
    wcel
    #
    @21
    cvv
    wcel
    @77
    @45
    wceq
    vi
    vex
    #
    vj
    vex
    vx
    vy
    @19
    @21
    cvv
    cvv
    @66
    @45
    cP
    @63
    @19
    wceq
    #
    @64
    @21
    wceq
    wa
    @65
    @24
    @5
    cmo
    @63
    @19
    @64
    @21
    cmul
    oveq12
    oveq1d
    elqaa.7
    @67
    ovmpt2a
    mp2an
    @76
    @24
    cz
    wcel
    @51
    @45
    cn0
    wcel
    @3
    @76
    @24
    @19
    @21
    nn0mulcl
    nn0zd
    @2
    wph
    @14
    @51
    @15
    @52
    sylan2
    #
    @24
    @5
    zmodcl
    syl2anr
    syl5eqel
    @3
    cn0
    cn0
    @11
    wf
    #
    @29
    @69
    cn0
    wcel
    @28
    @2
    wph
    @14
    @82
    @15
    @16
    vk
    cn0
    @10
    cn0
    @11
    @16
    @4
    cn0
    wcel
    #
    wa
    #
    @9
    @5
    @84
    @9
    wph
    @83
    @9
    cn
    wcel
    #
    @14
    wph
    @83
    wa
    @85
    @4
    cB
    cfv
    #
    @9
    cmul
    co
    cz
    wcel
    wph
    cA
    cB
    cR
    vm
    vn
    cF
    @4
    cN
    elqaa.1
    elqaa.2
    elqaa.3
    elqaa.4
    cN
    vk
    cn0
    @86
    vn
    cv
    #
    cmul
    co
    #
    cz
    wcel
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cmpt
    vm
    cn0
    vm
    cv
    #
    cB
    cfv
    #
    @87
    cmul
    co
    #
    cz
    wcel
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cmpt
    elqaa.5
    vk
    vm
    cn0
    @91
    @97
    @4
    @92
    wceq
    #
    cr
    @90
    @96
    clt
    @98
    @89
    @95
    vn
    cn
    @98
    @88
    @94
    cz
    @98
    @86
    @93
    @87
    cmul
    @4
    @92
    cB
    fveq2
    oveq1d
    eleq1d
    rabbidv
    infeq1d
    cbvmptv
    eqtri
    elqaa.6
    elqaalem1
    simpld
    adantlr
    nnzd
    @16
    @51
    @83
    @52
    adantr
    zmodcld
    @73
    fmptd
    sylan2
    @32
    cn0
    cn0
    @19
    @11
    ffvelrn
    syl2an
    @3
    @29
    wa
    #
    cc0
    @19
    cP
    co
    #
    cc0
    @19
    cmul
    co
    #
    @5
    cmo
    co
    #
    cc0
    cc0
    cvv
    wcel
    #
    @78
    @100
    @102
    wceq
    c0ex
    @79
    vx
    vy
    cc0
    @19
    cvv
    cvv
    @66
    @102
    cP
    @63
    cc0
    wceq
    @64
    @19
    wceq
    wa
    @65
    @101
    @5
    cmo
    @63
    cc0
    @64
    @19
    cmul
    oveq12
    oveq1d
    elqaa.7
    @101
    @5
    cmo
    ovex
    ovmpt2a
    mp2an
    @29
    @3
    @102
    cc0
    @5
    cmo
    co
    #
    cc0
    @29
    @101
    cc0
    @5
    cmo
    @29
    @19
    @19
    nn0cn
    #
    mul02d
    oveq1d
    @3
    @57
    @104
    cc0
    wceq
    @3
    @5
    @81
    nnrpd
    #
    @5
    0mod
    syl
    #
    sylan9eqr
    syl5eq
    @99
    @19
    cc0
    cP
    co
    #
    @19
    cc0
    cmul
    co
    #
    @5
    cmo
    co
    #
    cc0
    @78
    @103
    @108
    @110
    wceq
    @79
    c0ex
    vx
    vy
    @19
    cc0
    cvv
    cvv
    @66
    @110
    cP
    @80
    @64
    cc0
    wceq
    wa
    @65
    @109
    @5
    cmo
    @63
    @19
    @64
    cc0
    cmul
    oveq12
    oveq1d
    elqaa.7
    @109
    @5
    cmo
    ovex
    ovmpt2a
    mp2an
    @29
    @3
    @110
    @104
    cc0
    @29
    @109
    cc0
    @5
    cmo
    @29
    @19
    @105
    mul01d
    oveq1d
    @107
    sylan9eqr
    syl5eq
    wph
    @2
    simpr
    wph
    @38
    @2
    @39
    adantr
    @3
    cK
    @11
    cfv
    #
    @5
    @5
    cmo
    co
    #
    cc0
    @3
    @14
    @111
    @112
    wceq
    @2
    @14
    wph
    @15
    adantl
    vk
    cK
    @10
    @112
    cn0
    @11
    @4
    cK
    wceq
    @9
    @5
    @5
    cmo
    @4
    cK
    cN
    fveq2
    oveq1d
    @73
    @5
    @5
    cmo
    ovex
    fvmpt
    syl
    @3
    @112
    cc0
    wceq
    #
    @5
    @5
    cdiv
    co
    #
    cz
    wcel
    #
    @3
    @114
    c1
    cz
    @3
    @5
    @3
    @5
    @81
    nncnd
    @3
    @5
    @81
    nnne0d
    dividd
    1z
    syl6eqel
    @3
    @5
    cr
    wcel
    @57
    @113
    @115
    wb
    @3
    @5
    @81
    nnred
    @106
    @5
    @5
    mod0
    syl2anc
    mpbird
    eqtrd
    seqz
    3eqtr3d
end
