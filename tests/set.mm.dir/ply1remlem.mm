include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "c0g.mm"
include "wne.mm"
include "cco1.mm"
include "cur.mm"
include "co.mm"
include "cgrp.mm"
include "crg.mm"
include "cnzr.mm"
include "nzrring.mm"
include "syl.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "vr1cl.mm"
include "wf.mm"
include "ply1sclf.mm"
include "ffvelrnd.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "cn0.mm"
include "fveq2i.mm"
include "clt.mm"
include "cc0.mm"
include "cxr.mm"
include "deg1xrcl.mm"
include "0xr.mm"
include "a1i.mm"
include "cr.mm"
include "1re.mm"
include "rexr.mm"
include "mp1i.mm"
include "cle.mm"
include "wbr.mm"
include "deg1sclle.mm"
include "syl2anc.mm"
include "0lt1.mm"
include "xrlelttrd.mm"
include "cmgp.mm"
include "cmg.mm"
include "eqid.mm"
include "mgpbas.mm"
include "mulg1.mm"
include "fveq2d.mm"
include "1nn0.mm"
include "deg1pw.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "breqtrrd.mm"
include "deg1sub.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "syl6eqel.mm"
include "wb.mm"
include "deg1nn0clb.mm"
include "mpbird.mm"
include "csg.mm"
include "fveq1i.mm"
include "coe1subfv.mm"
include "syl31anc.mm"
include "cvsca.mm"
include "csca.mm"
include "oveq2d.mm"
include "ply1sca.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "lmodvs1.mm"
include "3eqtrd.mm"
include "fveq1d.mm"
include "ringidcl.mm"
include "coe1tmfv1.mm"
include "cv.mm"
include "cif.mm"
include "cmpt.mm"
include "coe1scl.mm"
include "ax-1ne0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "ifnefalse.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "grpsubid1.mm"
include "ismon1p.mm"
include "syl3anbrc.mm"
include "wa.mm"
include "ccrg.mm"
include "adantr.mm"
include "simpr.mm"
include "evl1vard.mm"
include "evl1scad.mm"
include "evl1subd.mm"
include "simprd.mm"
include "eqeq1d.mm"
include "grpsubeq0.mm"
include "bitrd.mm"
include "velsn.mm"
include "syl6bbr.mm"
include "pm5.32da.mm"
include "wfn.mm"
include "cpws.mm"
include "cbs.mm"
include "cvv.mm"
include "eqeltri.mm"
include "crh.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fniniseg.mm"
include "snssd.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "3jca.mm"

theorem ply1remlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cU: class U
  let cG: class G
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
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
  assume ply1rem.u: |- U = ( Monic1p ` R )
  assume ply1rem.d: |- D = ( deg1 ` R )
  assume ply1rem.z: |- .0. = ( 0g ` R )


  assert |- ( ph -> ( G e. U /\ ( D ` G ) = 1 /\ ( `' ( O ` G ) " { .0. } ) = { N } ) )

  proof
    wph
    cG
    cU
    wcel
    #
    cG
    cD
    cfv
    #
    c1
    wceq
    cG
    cO
    cfv
    #
    ccnv
    c.0
    csn
    cima
    #
    cN
    csn
    #
    wceq
    wph
    cG
    cB
    wcel
    #
    cG
    cP
    c0g
    cfv
    #
    wne
    #
    @1
    cG
    cco1
    cfv
    #
    cfv
    #
    cR
    cur
    cfv
    #
    wceq
    @0
    wph
    cG
    cX
    cN
    cA
    cfv
    #
    c.mi
    co
    #
    cB
    ply1rem.g
    wph
    cP
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    wph
    cP
    crg
    wcel
    #
    @13
    wph
    cR
    crg
    wcel
    #
    @17
    wph
    cR
    cnzr
    wcel
    #
    @18
    ply1rem.1
    cR
    nzrring
    syl
    #
    cP
    cR
    ply1rem.p
    ply1ring
    syl
    cP
    ringgrp
    syl
    wph
    @18
    @14
    @20
    cB
    cP
    cR
    cX
    ply1rem.x
    ply1rem.p
    ply1rem.b
    vr1cl
    syl
    #
    wph
    cK
    cB
    cN
    cA
    wph
    @18
    cK
    cB
    cA
    wf
    @20
    cA
    cB
    cP
    cR
    cK
    ply1rem.p
    ply1rem.a
    ply1rem.k
    ply1rem.b
    ply1sclf
    syl
    ply1rem.3
    ffvelrnd
    #
    cB
    cP
    c.mi
    cX
    @11
    ply1rem.b
    ply1rem.m
    grpsubcl
    syl3anc
    syl5eqel
    #
    wph
    @7
    @1
    cn0
    wcel
    #
    wph
    @1
    c1
    cn0
    wph
    @1
    cX
    cD
    cfv
    #
    c1
    wph
    @1
    @12
    cD
    cfv
    @25
    cG
    @12
    cD
    ply1rem.g
    fveq2i
    wph
    cB
    cD
    cR
    cX
    @11
    c.mi
    cP
    ply1rem.p
    ply1rem.d
    @20
    ply1rem.b
    ply1rem.m
    @21
    @22
    wph
    @11
    cD
    cfv
    #
    c1
    @25
    clt
    wph
    @26
    cc0
    c1
    wph
    @15
    @26
    cxr
    wcel
    @22
    cB
    cD
    cP
    cR
    @11
    ply1rem.d
    ply1rem.p
    ply1rem.b
    deg1xrcl
    syl
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    c1
    cr
    wcel
    c1
    cxr
    wcel
    wph
    1re
    c1
    rexr
    mp1i
    wph
    @18
    cN
    cK
    wcel
    #
    @26
    cc0
    cle
    wbr
    @20
    ply1rem.3
    cA
    cD
    cP
    cR
    cN
    cK
    ply1rem.d
    ply1rem.p
    ply1rem.k
    ply1rem.a
    deg1sclle
    syl2anc
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    xrlelttrd
    wph
    c1
    cX
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cD
    cfv
    #
    @25
    c1
    wph
    @30
    cX
    cD
    wph
    @14
    @30
    cX
    wceq
    @21
    cB
    @29
    @28
    cX
    cB
    cP
    @28
    @28
    eqid
    #
    ply1rem.b
    mgpbas
    @29
    eqid
    #
    mulg1
    syl
    #
    fveq2d
    wph
    @19
    c1
    cn0
    wcel
    #
    @31
    c1
    wceq
    ply1rem.1
    1nn0
    cD
    cP
    cR
    @29
    c1
    @28
    cX
    ply1rem.d
    ply1rem.p
    ply1rem.x
    @32
    @33
    deg1pw
    sylancl
    eqtr3d
    #
    breqtrrd
    deg1sub
    syl5eq
    @36
    eqtrd
    #
    1nn0
    syl6eqel
    wph
    @18
    @5
    @7
    @24
    wb
    @20
    @23
    cB
    cD
    cP
    cR
    cG
    @6
    ply1rem.d
    ply1rem.p
    @6
    eqid
    #
    ply1rem.b
    deg1nn0clb
    syl2anc
    mpbird
    wph
    @9
    c1
    @8
    cfv
    #
    c1
    cX
    cco1
    cfv
    #
    cfv
    #
    c1
    @11
    cco1
    cfv
    #
    cfv
    #
    cR
    csg
    cfv
    #
    co
    #
    @10
    wph
    @1
    c1
    @8
    @37
    fveq2d
    wph
    @39
    c1
    @12
    cco1
    cfv
    #
    cfv
    #
    @45
    c1
    @8
    @46
    cG
    @12
    cco1
    ply1rem.g
    fveq2i
    fveq1i
    wph
    @18
    @14
    @15
    @35
    @47
    @45
    wceq
    @20
    @21
    @22
    @35
    wph
    1nn0
    a1i
    #
    cB
    cR
    cX
    @11
    c.mi
    @44
    c1
    cP
    ply1rem.p
    ply1rem.b
    ply1rem.m
    @44
    eqid
    #
    coe1subfv
    syl31anc
    syl5eq
    wph
    @45
    @10
    cR
    c0g
    cfv
    #
    @44
    co
    #
    @10
    wph
    @41
    @10
    @43
    @50
    @44
    wph
    c1
    @10
    @30
    cP
    cvsca
    cfv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @41
    @10
    wph
    c1
    @54
    @40
    wph
    @53
    cX
    cco1
    wph
    @53
    @10
    cX
    @52
    co
    cP
    csca
    cfv
    #
    cur
    cfv
    #
    cX
    @52
    co
    #
    cX
    wph
    @30
    cX
    @10
    @52
    @34
    oveq2d
    wph
    @10
    @57
    cX
    @52
    wph
    cR
    @56
    cur
    wph
    @19
    cR
    @56
    wceq
    ply1rem.1
    cP
    cR
    cnzr
    ply1rem.p
    ply1sca
    syl
    fveq2d
    oveq1d
    wph
    cP
    clmod
    wcel
    #
    @14
    @58
    cX
    wceq
    wph
    @18
    @59
    @20
    cP
    cR
    ply1rem.p
    ply1lmod
    syl
    @21
    @52
    @57
    @56
    cB
    cP
    cX
    ply1rem.b
    @56
    eqid
    @52
    eqid
    #
    @57
    eqid
    lmodvs1
    syl2anc
    3eqtrd
    fveq2d
    fveq1d
    wph
    @18
    @10
    cK
    wcel
    #
    @35
    @55
    @10
    wceq
    @20
    wph
    @18
    @61
    @20
    cK
    cR
    @10
    ply1rem.k
    @10
    eqid
    #
    ringidcl
    syl
    #
    @48
    @10
    c1
    cP
    cR
    @52
    @29
    cK
    @28
    cX
    c.0
    ply1rem.z
    ply1rem.k
    ply1rem.p
    ply1rem.x
    @60
    @32
    @33
    coe1tmfv1
    syl3anc
    eqtr3d
    wph
    @43
    c1
    vx
    cn0
    vx
    cv
    #
    cc0
    wceq
    cN
    @50
    cif
    #
    cmpt
    #
    cfv
    #
    @50
    wph
    c1
    @42
    @66
    wph
    @18
    @27
    @42
    @66
    wceq
    @20
    ply1rem.3
    vx
    cA
    cP
    cR
    cK
    cN
    @50
    ply1rem.p
    ply1rem.a
    ply1rem.k
    @50
    eqid
    #
    coe1scl
    syl2anc
    fveq1d
    @35
    @67
    @50
    wceq
    1nn0
    vx
    c1
    @65
    @50
    cn0
    @66
    @64
    c1
    wceq
    #
    @64
    cc0
    wne
    #
    @65
    @50
    wceq
    @69
    @70
    c1
    cc0
    wne
    ax-1ne0
    @64
    c1
    cc0
    neeq1
    mpbiri
    @64
    cc0
    cN
    @50
    ifnefalse
    syl
    @66
    eqid
    cR
    c0g
    fvex
    fvmpt
    ax-mp
    syl6eq
    oveq12d
    wph
    cR
    cgrp
    wcel
    #
    @61
    @51
    @10
    wceq
    wph
    @18
    @71
    @20
    cR
    ringgrp
    syl
    #
    @63
    cK
    cR
    @44
    @10
    @50
    ply1rem.k
    @68
    @49
    grpsubid1
    syl2anc
    eqtrd
    3eqtrd
    cB
    cD
    cP
    cR
    @10
    cG
    cU
    @6
    ply1rem.p
    ply1rem.b
    @38
    ply1rem.d
    ply1rem.u
    @62
    ismon1p
    syl3anbrc
    @37
    wph
    vx
    @3
    @4
    wph
    @64
    cK
    wcel
    #
    @64
    @2
    cfv
    #
    c.0
    wceq
    #
    wa
    #
    @73
    @64
    @4
    wcel
    #
    wa
    @64
    @3
    wcel
    #
    @77
    wph
    @73
    @75
    @77
    wph
    @73
    wa
    #
    @75
    @64
    cN
    wceq
    #
    @77
    @79
    @75
    @64
    cN
    @44
    co
    #
    c.0
    wceq
    #
    @80
    @79
    @74
    @81
    c.0
    @79
    @74
    @64
    @12
    cO
    cfv
    #
    cfv
    #
    @81
    @64
    @2
    @83
    cG
    @12
    cO
    ply1rem.g
    fveq2i
    fveq1i
    @79
    @16
    @84
    @81
    wceq
    @79
    cK
    @44
    cP
    cR
    cB
    cX
    c.mi
    @11
    cO
    @64
    cN
    @64
    ply1rem.o
    ply1rem.p
    ply1rem.k
    ply1rem.b
    wph
    cR
    ccrg
    wcel
    #
    @73
    ply1rem.2
    adantr
    #
    wph
    @73
    simpr
    #
    @79
    cK
    cP
    cR
    cB
    cO
    cX
    @64
    ply1rem.o
    ply1rem.x
    ply1rem.k
    ply1rem.p
    ply1rem.b
    @86
    @87
    evl1vard
    @79
    cA
    cK
    cP
    cR
    cB
    cO
    cN
    @64
    ply1rem.o
    ply1rem.p
    ply1rem.k
    ply1rem.a
    ply1rem.b
    @86
    wph
    @27
    @73
    ply1rem.3
    adantr
    #
    @87
    evl1scad
    ply1rem.m
    @49
    evl1subd
    simprd
    syl5eq
    eqeq1d
    @79
    @71
    @73
    @27
    @82
    @80
    wb
    wph
    @71
    @73
    @72
    adantr
    @87
    @88
    cK
    cR
    @44
    @64
    cN
    c.0
    ply1rem.k
    ply1rem.z
    @49
    grpsubeq0
    syl3anc
    bitrd
    vx
    cN
    velsn
    syl6bbr
    pm5.32da
    wph
    @2
    cK
    wfn
    #
    @78
    @76
    wb
    wph
    cK
    cK
    @2
    wf
    @89
    wph
    cK
    cR
    cK
    cR
    cK
    cpws
    co
    #
    cbs
    cfv
    #
    cnzr
    @2
    @90
    cvv
    @90
    eqid
    #
    ply1rem.k
    @91
    eqid
    #
    ply1rem.1
    cK
    cvv
    wcel
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
    wph
    cB
    @91
    cG
    cO
    wph
    cO
    cP
    @90
    crh
    co
    wcel
    #
    cB
    @91
    cO
    wf
    wph
    @85
    @94
    ply1rem.2
    cK
    cP
    cR
    @90
    cO
    ply1rem.o
    ply1rem.p
    @92
    ply1rem.k
    evl1rhm
    syl
    cB
    @91
    cP
    @90
    cO
    ply1rem.b
    @93
    rhmf
    syl
    @23
    ffvelrnd
    pwselbas
    cK
    cK
    @2
    ffn
    syl
    cK
    c.0
    @64
    @2
    fniniseg
    syl
    wph
    @77
    @73
    wph
    @4
    cK
    @64
    wph
    cN
    cK
    ply1rem.3
    snssd
    sseld
    pm4.71rd
    3bitr4d
    eqrdv
    3jca
end
