include "co.mm"
include "cc0.mm"
include "cco1.mm"
include "cfv.mm"
include "cdg1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "cmnf.mm"
include "csn.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "crg.mm"
include "cuc1p.mm"
include "cnzr.mm"
include "nzrring.mm"
include "syl.mm"
include "cmn1.mm"
include "ccnv.mm"
include "c0g.mm"
include "cima.mm"
include "eqid.mm"
include "ply1remlem.mm"
include "simp1d.mm"
include "mon1puc1p.mm"
include "syl2anc.mm"
include "r1pdeglt.mm"
include "syl3anc.mm"
include "simp2d.mm"
include "breqtrd.mm"
include "1e0p1.mm"
include "syl6breq.mm"
include "wb.mm"
include "0nn0.mm"
include "nn0leltp1.mm"
include "mpan2.mm"
include "syl5ibrcom.mm"
include "wi.mm"
include "elsni.mm"
include "cxr.mm"
include "0xr.mm"
include "mnfle.mm"
include "ax-mp.mm"
include "syl6eqbr.mm"
include "a1i.mm"
include "cun.mm"
include "wo.mm"
include "r1pcl.mm"
include "deg1cl.mm"
include "elun.mm"
include "sylib.mm"
include "mpjaod.mm"
include "deg1le0.mm"
include "mpbid.mm"
include "cq1p.mm"
include "cmulr.mm"
include "cplusg.mm"
include "cof.mm"
include "cpws.mm"
include "r1pid.mm"
include "fveq2d.mm"
include "cghm.mm"
include "crh.mm"
include "ccrg.mm"
include "evl1rhm.mm"
include "rhmghm.mm"
include "ply1ring.mm"
include "q1pcl.mm"
include "mon1pcl.mm"
include "ringcl.mm"
include "ghmlin.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "pwsplusgval.mm"
include "3eqtrd.mm"
include "fveq1d.mm"
include "wfn.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "rhmmul.mm"
include "pwsmulrval.mm"
include "eqtrd.mm"
include "wa.mm"
include "snidg.mm"
include "simp3d.mm"
include "eleqtrrd.mm"
include "fniniseg.mm"
include "simprd.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "oveq1d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grplid.mm"
include "cxp.mm"
include "coe1f.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "evl1sca.mm"
include "fvconst2.mm"
include "eqtr4d.mm"

theorem ply1rem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cO: class O
  let cX: class X
  let vx: setvar x
  let c.0: class .0.
  assume ply1rem.p: |- P = ( Poly1 ` R )
  assume ply1rem.b: |- B = ( Base ` P )
  assume ply1rem.k: |- K = ( Base ` R )
  assume ply1rem.x: |- X = ( var1 ` R )
  assume ply1rem.m: |- .- = ( -g ` P )
  assume ply1rem.a: |- A = ( algSc ` P )
  assume ply1rem.g: |- G = ( X .- ( A ` N ) )
  assume ply1rem.o: |- O = ( eval1 ` R )
  assume ply1rem.1: |- ( ph -> R e. NzRing )
  assume ply1rem.2: |- ( ph -> R e. CRing )
  assume ply1rem.3: |- ( ph -> N e. K )
  assume ply1rem.4: |- ( ph -> F e. B )
  assume ply1rem.e: |- E = ( rem1p ` R )


  assert |- ( ph -> ( F E G ) = ( A ` ( ( O ` F ) ` N ) ) )

  proof
    wph
    cF
    cG
    cE
    co
    #
    cc0
    @0
    cco1
    cfv
    #
    cfv
    #
    cA
    cfv
    #
    cN
    cF
    cO
    cfv
    #
    cfv
    #
    cA
    cfv
    wph
    @0
    cR
    cdg1
    cfv
    #
    cfv
    #
    cc0
    cle
    wbr
    #
    @0
    @3
    wceq
    #
    wph
    @7
    cn0
    wcel
    #
    @8
    @7
    cmnf
    csn
    #
    wcel
    #
    wph
    @8
    @10
    @7
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wph
    @7
    c1
    @13
    clt
    wph
    @7
    cG
    @6
    cfv
    #
    c1
    clt
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
    @7
    @15
    clt
    wbr
    wph
    cR
    cnzr
    wcel
    @16
    ply1rem.1
    cR
    nzrring
    syl
    #
    ply1rem.4
    wph
    @16
    cG
    cR
    cmn1
    cfv
    #
    wcel
    #
    @19
    @20
    wph
    @22
    @15
    c1
    wceq
    #
    cG
    cO
    cfv
    #
    ccnv
    cR
    c0g
    cfv
    #
    csn
    cima
    #
    cN
    csn
    #
    wceq
    #
    wph
    cA
    cB
    @6
    cP
    cR
    @21
    cG
    cK
    c.mi
    cN
    cO
    cX
    @25
    ply1rem.p
    ply1rem.b
    ply1rem.k
    ply1rem.x
    ply1rem.m
    ply1rem.a
    ply1rem.g
    ply1rem.o
    ply1rem.1
    ply1rem.2
    ply1rem.3
    @21
    eqid
    #
    @6
    eqid
    #
    @25
    eqid
    #
    ply1remlem
    #
    simp1d
    #
    @18
    cR
    @21
    cG
    @18
    eqid
    #
    @29
    mon1puc1p
    syl2anc
    #
    cB
    @18
    @6
    cP
    cR
    cE
    cF
    cG
    ply1rem.e
    ply1rem.p
    ply1rem.b
    @34
    @30
    r1pdeglt
    syl3anc
    wph
    @22
    @23
    @28
    @32
    simp2d
    breqtrd
    1e0p1
    syl6breq
    @10
    cc0
    cn0
    wcel
    #
    @8
    @14
    wb
    0nn0
    @7
    cc0
    nn0leltp1
    mpan2
    syl5ibrcom
    @12
    @8
    wi
    wph
    @12
    @7
    cmnf
    cc0
    cle
    @7
    cmnf
    elsni
    cc0
    cxr
    wcel
    cmnf
    cc0
    cle
    wbr
    0xr
    cc0
    mnfle
    ax-mp
    syl6eqbr
    a1i
    wph
    @7
    cn0
    @11
    cun
    wcel
    #
    @10
    @12
    wo
    wph
    @0
    cB
    wcel
    #
    @37
    wph
    @16
    @17
    @19
    @38
    @20
    ply1rem.4
    @35
    cB
    @18
    cP
    cR
    cE
    cF
    cG
    ply1rem.e
    ply1rem.p
    ply1rem.b
    @34
    r1pcl
    syl3anc
    #
    cB
    @6
    cP
    cR
    @0
    @30
    ply1rem.p
    ply1rem.b
    deg1cl
    syl
    @7
    cn0
    @11
    elun
    sylib
    mpjaod
    wph
    @16
    @38
    @8
    @9
    wb
    @20
    @39
    cA
    cB
    @6
    cP
    cR
    @0
    @30
    ply1rem.p
    ply1rem.b
    ply1rem.a
    deg1le0
    syl2anc
    mpbid
    #
    wph
    @5
    @2
    cA
    wph
    @5
    cN
    cF
    cG
    cR
    cq1p
    cfv
    #
    co
    #
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
    @0
    cO
    cfv
    #
    cR
    cplusg
    cfv
    #
    cof
    co
    #
    cfv
    #
    cN
    @46
    cfv
    #
    @2
    wph
    cN
    @4
    @48
    wph
    @4
    @44
    @0
    cP
    cplusg
    cfv
    #
    co
    #
    cO
    cfv
    #
    @45
    @46
    cR
    cK
    cpws
    co
    #
    cplusg
    cfv
    #
    co
    #
    @48
    wph
    cF
    @52
    cO
    wph
    @16
    @17
    @19
    cF
    @52
    wceq
    @20
    ply1rem.4
    @35
    cB
    @18
    cP
    @51
    @41
    cR
    @43
    cE
    cF
    cG
    ply1rem.p
    ply1rem.b
    @34
    @41
    eqid
    #
    ply1rem.e
    @43
    eqid
    #
    @51
    eqid
    #
    r1pid
    syl3anc
    fveq2d
    wph
    cO
    cP
    @54
    cghm
    co
    wcel
    #
    @44
    cB
    wcel
    #
    @38
    @53
    @56
    wceq
    wph
    cO
    cP
    @54
    crh
    co
    wcel
    #
    @60
    wph
    cR
    ccrg
    wcel
    #
    @62
    ply1rem.2
    cK
    cP
    cR
    @54
    cO
    ply1rem.o
    ply1rem.p
    @54
    eqid
    #
    ply1rem.k
    evl1rhm
    syl
    #
    cP
    @54
    cO
    rhmghm
    syl
    wph
    cP
    crg
    wcel
    #
    @42
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    @61
    wph
    @16
    @66
    @20
    cP
    cR
    ply1rem.p
    ply1ring
    syl
    wph
    @16
    @17
    @19
    @67
    @20
    ply1rem.4
    @35
    cB
    @18
    cP
    @41
    cR
    cF
    cG
    @57
    ply1rem.p
    ply1rem.b
    @34
    q1pcl
    syl3anc
    #
    wph
    @22
    @68
    @33
    cB
    cP
    cR
    cG
    @21
    ply1rem.p
    ply1rem.b
    @29
    mon1pcl
    syl
    #
    cB
    cP
    @43
    @42
    cG
    ply1rem.b
    @58
    ringcl
    syl3anc
    #
    @39
    @51
    @55
    cP
    @54
    @44
    cO
    @0
    cB
    ply1rem.b
    @59
    @55
    eqid
    #
    ghmlin
    syl3anc
    wph
    @54
    cbs
    cfv
    #
    @47
    @55
    cR
    @45
    @46
    cK
    cnzr
    cvv
    @54
    @64
    @73
    eqid
    #
    ply1rem.1
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
    ply1rem.k
    cR
    cbs
    fvex
    eqeltri
    a1i
    #
    wph
    cB
    @73
    @44
    cO
    wph
    @62
    cB
    @73
    cO
    wf
    @65
    cB
    @73
    cP
    @54
    cO
    ply1rem.b
    @74
    rhmf
    syl
    #
    @71
    ffvelrnd
    #
    wph
    cB
    @73
    @0
    cO
    @77
    @39
    ffvelrnd
    #
    @47
    eqid
    #
    @72
    pwsplusgval
    3eqtrd
    fveq1d
    wph
    @49
    cN
    @45
    cfv
    #
    @50
    @47
    co
    #
    @25
    @50
    @47
    co
    #
    @50
    wph
    @45
    cK
    wfn
    #
    @46
    cK
    wfn
    #
    @75
    cN
    cK
    wcel
    #
    @49
    @82
    wceq
    wph
    cK
    cK
    @45
    wf
    @84
    wph
    cK
    cR
    cK
    @73
    cnzr
    @45
    @54
    cvv
    @64
    ply1rem.k
    @74
    ply1rem.1
    @76
    @78
    pwselbas
    cK
    cK
    @45
    ffn
    syl
    wph
    cK
    cK
    @46
    wf
    @85
    wph
    cK
    cR
    cK
    @73
    cnzr
    @46
    @54
    cvv
    @64
    ply1rem.k
    @74
    ply1rem.1
    @76
    @79
    pwselbas
    #
    cK
    cK
    @46
    ffn
    syl
    @76
    ply1rem.3
    cK
    @47
    @45
    @46
    cvv
    cN
    fnfvof
    syl22anc
    wph
    @81
    @25
    @50
    @47
    wph
    @81
    cN
    @42
    cO
    cfv
    #
    @24
    cR
    cmulr
    cfv
    #
    cof
    co
    #
    cfv
    #
    cN
    @88
    cfv
    #
    cN
    @24
    cfv
    #
    @89
    co
    #
    @25
    wph
    cN
    @45
    @90
    wph
    @45
    @88
    @24
    @54
    cmulr
    cfv
    #
    co
    #
    @90
    wph
    @62
    @67
    @68
    @45
    @96
    wceq
    @65
    @69
    @70
    @42
    cG
    cP
    @54
    @43
    @95
    cO
    cB
    ply1rem.b
    @58
    @95
    eqid
    #
    rhmmul
    syl3anc
    wph
    @73
    cR
    @95
    @89
    @88
    @24
    cK
    cnzr
    cvv
    @54
    @64
    @74
    ply1rem.1
    @76
    wph
    cB
    @73
    @42
    cO
    @77
    @69
    ffvelrnd
    #
    wph
    cB
    @73
    cG
    cO
    @77
    @70
    ffvelrnd
    #
    @89
    eqid
    #
    @97
    pwsmulrval
    eqtrd
    fveq1d
    wph
    @88
    cK
    wfn
    #
    @24
    cK
    wfn
    #
    @75
    @86
    @91
    @94
    wceq
    wph
    cK
    cK
    @88
    wf
    @101
    wph
    cK
    cR
    cK
    @73
    cnzr
    @88
    @54
    cvv
    @64
    ply1rem.k
    @74
    ply1rem.1
    @76
    @98
    pwselbas
    #
    cK
    cK
    @88
    ffn
    syl
    wph
    cK
    cK
    @24
    wf
    @102
    wph
    cK
    cR
    cK
    @73
    cnzr
    @24
    @54
    cvv
    @64
    ply1rem.k
    @74
    ply1rem.1
    @76
    @99
    pwselbas
    cK
    cK
    @24
    ffn
    syl
    #
    @76
    ply1rem.3
    cK
    @89
    @88
    @24
    cvv
    cN
    fnfvof
    syl22anc
    wph
    @94
    @92
    @25
    @89
    co
    #
    @25
    wph
    @93
    @25
    @92
    @89
    wph
    @86
    @93
    @25
    wceq
    #
    wph
    cN
    @26
    wcel
    #
    @86
    @106
    wa
    #
    wph
    cN
    @27
    @26
    wph
    @86
    cN
    @27
    wcel
    ply1rem.3
    cN
    cK
    snidg
    syl
    wph
    @22
    @23
    @28
    @32
    simp3d
    eleqtrrd
    wph
    @102
    @107
    @108
    wb
    @104
    cK
    @25
    cN
    @24
    fniniseg
    syl
    mpbid
    simprd
    oveq2d
    wph
    @16
    @92
    cK
    wcel
    @105
    @25
    wceq
    @20
    wph
    cK
    cK
    cN
    @88
    @103
    ply1rem.3
    ffvelrnd
    cK
    cR
    @89
    @92
    @25
    ply1rem.k
    @100
    @31
    ringrz
    syl2anc
    eqtrd
    3eqtrd
    oveq1d
    wph
    cR
    cgrp
    wcel
    #
    @50
    cK
    wcel
    @83
    @50
    wceq
    wph
    @16
    @109
    @20
    cR
    ringgrp
    syl
    wph
    cK
    cK
    cN
    @46
    @87
    ply1rem.3
    ffvelrnd
    cK
    @47
    cR
    @50
    @25
    ply1rem.k
    @80
    @31
    grplid
    syl2anc
    3eqtrd
    wph
    @50
    cN
    cK
    @2
    csn
    cxp
    #
    cfv
    #
    @2
    wph
    cN
    @46
    @110
    wph
    @46
    @3
    cO
    cfv
    #
    @110
    wph
    @0
    @3
    cO
    @40
    fveq2d
    wph
    @63
    @2
    cK
    wcel
    #
    @112
    @110
    wceq
    ply1rem.2
    wph
    cn0
    cK
    @1
    wf
    #
    @36
    @113
    wph
    @38
    @114
    @39
    @1
    cB
    cP
    cR
    @0
    cK
    @1
    eqid
    ply1rem.b
    ply1rem.p
    ply1rem.k
    coe1f
    syl
    0nn0
    cn0
    cK
    cc0
    @1
    ffvelrn
    sylancl
    cA
    cK
    cP
    cR
    cO
    @2
    ply1rem.o
    ply1rem.p
    ply1rem.k
    ply1rem.a
    evl1sca
    syl2anc
    eqtrd
    fveq1d
    wph
    @86
    @111
    @2
    wceq
    ply1rem.3
    cK
    @2
    cN
    cc0
    @1
    fvex
    fvconst2
    syl
    eqtrd
    3eqtrd
    fveq2d
    eqtr4d
end
