include "cv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "c0p.mm"
include "idd.mm"
include "wne.mm"
include "cdgr.mm"
include "cfv.mm"
include "ccoe.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cply.mm"
include "wcel.mm"
include "cn0.mm"
include "plydivlem2.mm"
include "mpdan.mm"
include "plysub.mm"
include "dgrcl.mm"
include "syl.mm"
include "nn0red.mm"
include "cr.mm"
include "ifcld.mm"
include "eqid.mm"
include "dgrsub.mm"
include "syl2anc.mm"
include "clt.mm"
include "wo.mm"
include "wb.mm"
include "dgrlt.mm"
include "mpbid.mm"
include "simpld.mm"
include "breq1.mm"
include "ifboth.mm"
include "letrd.mm"
include "adantr.mm"
include "caddc.mm"
include "nn0addge1.mm"
include "cmul.mm"
include "cmpt.mm"
include "wf.mm"
include "plyf.mm"
include "ffvelrnda.mm"
include "plymul.mm"
include "nnncan1d.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "subcld.mm"
include "feqmptd.mm"
include "offval2.mm"
include "syl5eq.mm"
include "3eqtr4d.mm"
include "w3a.mm"
include "subdi.mm"
include "adantl.mm"
include "caofdi.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "simpr.mm"
include "dgrmul.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "coesub.mm"
include "fveq1d.mm"
include "wfn.mm"
include "coef3.mm"
include "ffn.mm"
include "3syl.mm"
include "nn0ex.mm"
include "inidm.mm"
include "simprd.mm"
include "ofval.mm"
include "0m0e0.mm"
include "syl6eq.mm"
include "dgreq0.mm"
include "biimpar.mm"
include "syldan.mm"
include "ex.mm"
include "plymul0or.mm"
include "eqeq1d.mm"
include "wn.mm"
include "neneqd.mm"
include "biorf.mm"
include "3bitr4d.mm"
include "sylibd.mm"
include "pm2.61dne.mm"
include "df-0p.mm"
include "ofsubeq0.mm"
include "syl3anc.mm"

theorem plydiveu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vq: setvar q
  let vp: setvar p
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  let vf: setvar f
  let cH: class H
  let cB: class B
  let cD: class D
  let cM: class M
  let cN: class N
  let vg: setvar g
  let vw: setvar w
  assume plydiv.pl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plydiv.tm: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume plydiv.rc: |- ( ( ph /\ ( x e. S /\ x =/= 0 ) ) -> ( 1 / x ) e. S )
  assume plydiv.m1: |- ( ph -> -u 1 e. S )
  assume plydiv.f: |- ( ph -> F e. ( Poly ` S ) )
  assume plydiv.g: |- ( ph -> G e. ( Poly ` S ) )
  assume plydiv.z: |- ( ph -> G =/= 0p )
  assume plydiv.r: |- R = ( F oF - ( G oF x. q ) )
  assume plydiveu.q: |- ( ph -> q e. ( Poly ` S ) )
  assume plydiveu.qd: |- ( ph -> ( R = 0p \/ ( deg ` R ) < ( deg ` G ) ) )
  assume plydiveu.t: |- T = ( F oF - ( G oF x. p ) )
  assume plydiveu.p: |- ( ph -> p e. ( Poly ` S ) )
  assume plydiveu.pd: |- ( ph -> ( T = 0p \/ ( deg ` T ) < ( deg ` G ) ) )

  disjoint x y
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint F p
  disjoint q x
  disjoint q y
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint T x
  disjoint T y
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint G y
  disjoint R p
  disjoint R x
  disjoint R y
  disjoint S p
  disjoint S q
  disjoint S x
  disjoint S y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint p z
  disjoint q z
  disjoint F z
  disjoint H f
  disjoint H p
  disjoint H q
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint d ph
  disjoint ph z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N f
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint d g
  disjoint d w
  disjoint G d
  disjoint f g
  disjoint f w
  disjoint G f
  disjoint g p
  disjoint g q
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p w
  disjoint q w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint R d
  disjoint R f
  disjoint S d
  disjoint S f
  disjoint S g
  disjoint S z
  assert |- ( ph -> p = q )

  proof
    wph
    vp
    cv
    #
    vq
    cv
    #
    cmin
    cof
    #
    co
    #
    cc
    cc0
    csn
    cxp
    #
    wceq
    #
    @0
    @1
    wceq
    #
    wph
    @3
    c0p
    @4
    wph
    @3
    c0p
    wceq
    #
    @3
    c0p
    wph
    @7
    idd
    wph
    @3
    c0p
    wne
    #
    cR
    cT
    @2
    co
    #
    c0p
    wceq
    #
    @7
    wph
    @8
    @10
    wph
    @8
    @9
    cdgr
    cfv
    #
    @9
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    @10
    wph
    @8
    wa
    #
    @13
    cG
    cdgr
    cfv
    #
    @12
    cfv
    #
    cc0
    @15
    @11
    @16
    @12
    @15
    @11
    @16
    wceq
    #
    @11
    @16
    cle
    wbr
    #
    @16
    @11
    cle
    wbr
    #
    wph
    @19
    @8
    wph
    @11
    cR
    cdgr
    cfv
    #
    cT
    cdgr
    cfv
    #
    cle
    wbr
    #
    @22
    @21
    cif
    #
    @16
    wph
    @11
    wph
    @9
    cS
    cply
    cfv
    #
    wcel
    #
    @11
    cn0
    wcel
    wph
    vx
    vy
    cS
    cR
    cT
    wph
    @1
    @25
    wcel
    #
    cR
    @25
    wcel
    #
    plydiveu.q
    wph
    vx
    vy
    cR
    cS
    cF
    cG
    vq
    plydiv.pl
    plydiv.tm
    plydiv.rc
    plydiv.m1
    plydiv.f
    plydiv.g
    plydiv.z
    plydiv.r
    plydivlem2
    mpdan
    #
    wph
    @0
    @25
    wcel
    #
    cT
    @25
    wcel
    #
    plydiveu.p
    wph
    vx
    vy
    cT
    cS
    cF
    cG
    vp
    plydiv.pl
    plydiv.tm
    plydiv.rc
    plydiv.m1
    plydiv.f
    plydiv.g
    plydiv.z
    plydiveu.t
    plydivlem2
    mpdan
    #
    plydiv.pl
    plydiv.tm
    plydiv.m1
    plysub
    #
    cS
    @9
    dgrcl
    syl
    nn0red
    #
    wph
    @23
    @22
    @21
    cr
    wph
    @22
    wph
    @31
    @22
    cn0
    wcel
    @32
    cS
    cT
    dgrcl
    syl
    nn0red
    wph
    @21
    wph
    @28
    @21
    cn0
    wcel
    @29
    cS
    cR
    dgrcl
    syl
    nn0red
    ifcld
    wph
    @16
    wph
    cG
    @25
    wcel
    #
    @16
    cn0
    wcel
    #
    plydiv.g
    cS
    cG
    dgrcl
    syl
    #
    nn0red
    #
    wph
    @28
    @31
    @11
    @24
    cle
    wbr
    @29
    @32
    cS
    cR
    cT
    @21
    @22
    @21
    eqid
    #
    @22
    eqid
    #
    dgrsub
    syl2anc
    wph
    @22
    @16
    cle
    wbr
    #
    @21
    @16
    cle
    wbr
    #
    @24
    @16
    cle
    wbr
    #
    wph
    @41
    @16
    cT
    ccoe
    cfv
    #
    cfv
    cc0
    wceq
    #
    wph
    cT
    c0p
    wceq
    @22
    @16
    clt
    wbr
    wo
    #
    @41
    @45
    wa
    #
    plydiveu.pd
    wph
    @31
    @36
    @46
    @47
    wb
    @32
    @37
    @44
    cS
    cT
    @16
    @22
    @40
    @44
    eqid
    #
    dgrlt
    syl2anc
    mpbid
    #
    simpld
    wph
    @42
    @16
    cR
    ccoe
    cfv
    #
    cfv
    cc0
    wceq
    #
    wph
    cR
    c0p
    wceq
    @21
    @16
    clt
    wbr
    wo
    #
    @42
    @51
    wa
    #
    plydiveu.qd
    wph
    @28
    @36
    @52
    @53
    wb
    @29
    @37
    @50
    cS
    cR
    @16
    @21
    @39
    @50
    eqid
    #
    dgrlt
    syl2anc
    mpbid
    #
    simpld
    @23
    @41
    @42
    @43
    @22
    @21
    @22
    @24
    @16
    cle
    breq1
    @21
    @24
    @16
    cle
    breq1
    ifboth
    syl2anc
    letrd
    adantr
    @15
    @16
    @16
    @3
    cdgr
    cfv
    #
    caddc
    co
    #
    @11
    cle
    wph
    @16
    @57
    cle
    wbr
    #
    @8
    wph
    @16
    cr
    wcel
    @56
    cn0
    wcel
    #
    @58
    @38
    wph
    @3
    @25
    wcel
    #
    @59
    wph
    vx
    vy
    cS
    @0
    @1
    plydiveu.p
    plydiveu.q
    plydiv.pl
    plydiv.tm
    plydiv.m1
    plysub
    #
    cS
    @3
    dgrcl
    syl
    @16
    @56
    nn0addge1
    syl2anc
    adantr
    @15
    @11
    cG
    @3
    cmul
    cof
    #
    co
    #
    cdgr
    cfv
    #
    @57
    wph
    @11
    @64
    wceq
    @8
    wph
    @9
    @63
    cdgr
    wph
    @9
    cG
    @0
    @62
    co
    #
    cG
    @1
    @62
    co
    #
    @2
    co
    #
    @63
    wph
    vz
    cc
    vz
    cv
    #
    cF
    cfv
    #
    @68
    @66
    cfv
    #
    cmin
    co
    #
    @69
    @68
    @65
    cfv
    #
    cmin
    co
    #
    cmin
    co
    #
    cmpt
    vz
    cc
    @72
    @70
    cmin
    co
    #
    cmpt
    @9
    @67
    wph
    vz
    cc
    @74
    @75
    wph
    @68
    cc
    wcel
    #
    wa
    #
    @69
    @70
    @72
    wph
    cc
    cc
    @68
    cF
    wph
    cF
    @25
    wcel
    cc
    cc
    cF
    wf
    plydiv.f
    cS
    cF
    plyf
    syl
    #
    ffvelrnda
    #
    wph
    cc
    cc
    @68
    @66
    wph
    @66
    @25
    wcel
    cc
    cc
    @66
    wf
    wph
    vx
    vy
    cS
    cG
    @1
    plydiv.g
    plydiveu.q
    plydiv.pl
    plydiv.tm
    plymul
    cS
    @66
    plyf
    syl
    #
    ffvelrnda
    #
    wph
    cc
    cc
    @68
    @65
    wph
    @65
    @25
    wcel
    cc
    cc
    @65
    wf
    wph
    vx
    vy
    cS
    cG
    @0
    plydiv.g
    plydiveu.p
    plydiv.pl
    plydiv.tm
    plymul
    cS
    @65
    plyf
    syl
    #
    ffvelrnda
    #
    nnncan1d
    mpteq2dva
    wph
    vz
    cc
    @71
    @73
    cmin
    cR
    cT
    cvv
    cc
    cc
    cc
    cvv
    wcel
    #
    wph
    cnex
    a1i
    #
    @77
    @69
    @70
    @79
    @81
    subcld
    @77
    @69
    @72
    @79
    @83
    subcld
    wph
    cR
    cF
    @66
    @2
    co
    vz
    cc
    @71
    cmpt
    plydiv.r
    wph
    vz
    cc
    @69
    @70
    cmin
    cF
    @66
    cvv
    cc
    cc
    @85
    @79
    @81
    wph
    vz
    cc
    cc
    cF
    @78
    feqmptd
    #
    wph
    vz
    cc
    cc
    @66
    @80
    feqmptd
    #
    offval2
    syl5eq
    wph
    cT
    cF
    @65
    @2
    co
    vz
    cc
    @73
    cmpt
    plydiveu.t
    wph
    vz
    cc
    @69
    @72
    cmin
    cF
    @65
    cvv
    cc
    cc
    @85
    @79
    @83
    @86
    wph
    vz
    cc
    cc
    @65
    @82
    feqmptd
    #
    offval2
    syl5eq
    offval2
    wph
    vz
    cc
    @72
    @70
    cmin
    @65
    @66
    cvv
    cc
    cc
    @85
    @83
    @81
    @88
    @87
    offval2
    3eqtr4d
    wph
    vx
    vy
    vz
    cc
    cmin
    cc
    cmul
    cG
    @0
    @1
    cc
    cmin
    cvv
    @85
    wph
    @35
    cc
    cc
    cG
    wf
    plydiv.g
    cS
    cG
    plyf
    syl
    wph
    @30
    cc
    cc
    @0
    wf
    #
    plydiveu.p
    cS
    @0
    plyf
    syl
    #
    wph
    @27
    cc
    cc
    @1
    wf
    #
    plydiveu.q
    cS
    @1
    plyf
    syl
    #
    vx
    cv
    #
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    @76
    w3a
    @93
    @94
    @68
    cmin
    co
    cmul
    co
    @93
    @94
    cmul
    co
    @93
    @68
    cmul
    co
    cmin
    co
    wceq
    wph
    @93
    @94
    @68
    subdi
    adantl
    caofdi
    eqtr4d
    #
    fveq2d
    adantr
    @15
    @35
    cG
    c0p
    wne
    #
    @60
    @8
    @64
    @57
    wceq
    wph
    @35
    @8
    plydiv.g
    adantr
    wph
    @96
    @8
    plydiv.z
    adantr
    wph
    @60
    @8
    @61
    adantr
    wph
    @8
    simpr
    cS
    cG
    @3
    @16
    @56
    @16
    eqid
    @56
    eqid
    dgrmul
    syl22anc
    eqtrd
    breqtrrd
    wph
    @18
    @19
    @20
    wa
    wb
    @8
    wph
    @11
    @16
    @34
    @38
    letri3d
    adantr
    mpbir2and
    fveq2d
    wph
    @17
    cc0
    wceq
    @8
    wph
    @17
    cc0
    cc0
    cmin
    co
    #
    cc0
    wph
    @17
    @16
    @50
    @44
    @2
    co
    #
    cfv
    #
    @97
    wph
    @16
    @12
    @98
    wph
    @28
    @31
    @12
    @98
    wceq
    @29
    @32
    @50
    @44
    cS
    cR
    cT
    @54
    @48
    coesub
    syl2anc
    fveq1d
    wph
    @36
    @99
    @97
    wceq
    @37
    wph
    cn0
    cn0
    cc0
    cc0
    cmin
    cn0
    @50
    @44
    cvv
    cvv
    @16
    wph
    @28
    cn0
    cc
    @50
    wf
    @50
    cn0
    wfn
    @29
    @50
    cS
    cR
    @54
    coef3
    cn0
    cc
    @50
    ffn
    3syl
    wph
    @31
    cn0
    cc
    @44
    wf
    @44
    cn0
    wfn
    @32
    @44
    cS
    cT
    @48
    coef3
    cn0
    cc
    @44
    ffn
    3syl
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    #
    @100
    cn0
    inidm
    wph
    @51
    @36
    wph
    @42
    @51
    @55
    simprd
    adantr
    wph
    @45
    @36
    wph
    @41
    @45
    @49
    simprd
    adantr
    ofval
    mpdan
    eqtrd
    0m0e0
    syl6eq
    adantr
    eqtrd
    wph
    @10
    @14
    wph
    @26
    @10
    @14
    wb
    @33
    @12
    cS
    @9
    @11
    @11
    eqid
    @12
    eqid
    dgreq0
    syl
    biimpar
    syldan
    ex
    wph
    @63
    c0p
    wceq
    #
    cG
    c0p
    wceq
    #
    @7
    wo
    #
    @10
    @7
    wph
    @35
    @60
    @101
    @103
    wb
    plydiv.g
    @61
    cS
    cG
    @3
    plymul0or
    syl2anc
    wph
    @9
    @63
    c0p
    @95
    eqeq1d
    wph
    @102
    wn
    @7
    @103
    wb
    wph
    cG
    c0p
    plydiv.z
    neneqd
    @102
    @7
    biorf
    syl
    3bitr4d
    sylibd
    pm2.61dne
    df-0p
    syl6eq
    wph
    @84
    @89
    @91
    @5
    @6
    wb
    @85
    @90
    @92
    cc
    @0
    @1
    cvv
    ofsubeq0
    syl3anc
    mpbid
end
