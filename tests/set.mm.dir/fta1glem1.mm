include "c1.mm"
include "cq1p.mm"
include "cfv.mm"
include "co.mm"
include "1cnd.mm"
include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "cn0.mm"
include "cnzr.mm"
include "cidom.mm"
include "cdomn.mm"
include "ccrg.mm"
include "isidom.mm"
include "simprbi.mm"
include "domnnzr.mm"
include "syl.mm"
include "nzrring.mm"
include "cuc1p.mm"
include "cmn1.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "simplbi.mm"
include "wa.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "cpws.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "crh.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbid.mm"
include "simpld.mm"
include "ply1remlem.mm"
include "simp1d.mm"
include "mon1puc1p.mm"
include "syl2anc.mm"
include "q1pcl.mm"
include "syl3anc.mm"
include "cmulr.mm"
include "caddc.mm"
include "peano2nn0.mm"
include "eqeltrd.mm"
include "deg1nn0clb.mm"
include "mpbird.mm"
include "cdsr.mm"
include "wbr.mm"
include "simprd.mm"
include "facth1.mm"
include "dvdsq1p.mm"
include "eqcomd.mm"
include "ply1crng.mm"
include "crngring.mm"
include "mon1pcl.mm"
include "ringlz.mm"
include "3netr4d.mm"
include "oveq1.mm"
include "necon3i.mm"
include "deg1nn0cl.mm"
include "nn0cnd.mm"
include "crngcom.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "crlreg.mm"
include "simp2d.mm"
include "1nn0.mm"
include "syl6eqel.mm"
include "cui.mm"
include "cco1.mm"
include "wss.mm"
include "unitrrg.mm"
include "uc1pldg.mm"
include "sseldd.mm"
include "deg1mul2.mm"
include "3eqtr3d.mm"
include "cc.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "3eqtr3rd.mm"
include "addcanad.mm"

theorem fta1glem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
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
  let vg: setvar g
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


  assert |- ( ph -> ( D ` ( F ( quot1p ` R ) G ) ) = N )

  proof
    wph
    c1
    cF
    cG
    cR
    cq1p
    cfv
    #
    co
    #
    cD
    cfv
    #
    cN
    wph
    1cnd
    wph
    @2
    wph
    cR
    crg
    wcel
    #
    @1
    cB
    wcel
    #
    @1
    c.0
    wne
    #
    @2
    cn0
    wcel
    wph
    cR
    cnzr
    wcel
    #
    @3
    wph
    cR
    cidom
    wcel
    #
    @6
    fta1g.1
    @7
    cR
    cdomn
    wcel
    #
    @6
    @7
    cR
    ccrg
    wcel
    #
    @8
    cR
    isidom
    #
    simprbi
    cR
    domnnzr
    syl
    syl
    #
    cR
    nzrring
    syl
    #
    wph
    @3
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
    @4
    @12
    fta1g.2
    wph
    @3
    cG
    cR
    cmn1
    cfv
    #
    wcel
    #
    @15
    @12
    wph
    @17
    cG
    cD
    cfv
    #
    c1
    wceq
    #
    cG
    cO
    cfv
    ccnv
    cW
    csn
    #
    cima
    cT
    csn
    wceq
    #
    wph
    cA
    cB
    cD
    cP
    cR
    @16
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
    @11
    wph
    @7
    @9
    fta1g.1
    @7
    @9
    @8
    @10
    simplbi
    syl
    #
    wph
    cT
    cK
    wcel
    #
    cT
    cF
    cO
    cfv
    #
    cfv
    cW
    wceq
    #
    wph
    cT
    @24
    ccnv
    @20
    cima
    wcel
    #
    @23
    @25
    wa
    #
    fta1glem.5
    wph
    @24
    cK
    wfn
    #
    @26
    @27
    wb
    wph
    cK
    cK
    @24
    wf
    @28
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
    cidom
    @24
    @29
    cvv
    @29
    eqid
    #
    fta1glem.k
    @30
    eqid
    #
    fta1g.1
    cK
    cvv
    wcel
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
    a1i
    wph
    cB
    @30
    cF
    cO
    wph
    cO
    cP
    @29
    crh
    co
    wcel
    #
    cB
    @30
    cO
    wf
    wph
    @9
    @33
    @22
    cK
    cP
    cR
    @29
    cO
    fta1g.o
    fta1g.p
    @31
    fta1glem.k
    evl1rhm
    syl
    cB
    @30
    cP
    @29
    cO
    fta1g.b
    @32
    rhmf
    syl
    fta1g.2
    ffvelrnd
    pwselbas
    cK
    cK
    @24
    ffn
    syl
    cK
    cW
    cT
    @24
    fniniseg
    syl
    mpbid
    #
    simpld
    #
    @16
    eqid
    #
    fta1g.d
    fta1g.w
    ply1remlem
    #
    simp1d
    #
    @14
    cR
    @16
    cG
    @14
    eqid
    #
    @36
    mon1puc1p
    syl2anc
    #
    cB
    @14
    cP
    @0
    cR
    cF
    cG
    @0
    eqid
    #
    fta1g.p
    fta1g.b
    @39
    q1pcl
    syl3anc
    #
    wph
    @1
    cG
    cP
    cmulr
    cfv
    #
    co
    #
    c.0
    cG
    @43
    co
    #
    wne
    @5
    wph
    cF
    c.0
    @44
    @45
    wph
    cF
    c.0
    wne
    #
    cF
    cD
    cfv
    #
    cn0
    wcel
    #
    wph
    @47
    cN
    c1
    caddc
    co
    #
    cn0
    fta1glem.4
    wph
    cN
    cn0
    wcel
    @49
    cn0
    wcel
    fta1glem.3
    cN
    peano2nn0
    syl
    eqeltrd
    wph
    @3
    @13
    @46
    @48
    wb
    @12
    fta1g.2
    cB
    cD
    cP
    cR
    cF
    c.0
    fta1g.d
    fta1g.p
    fta1g.z
    fta1g.b
    deg1nn0clb
    syl2anc
    mpbird
    wph
    cF
    @44
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
    @44
    wceq
    #
    wph
    @51
    @25
    wph
    @23
    @25
    @34
    simprd
    wph
    cA
    cB
    @50
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
    @11
    @22
    @35
    fta1g.2
    fta1g.w
    @50
    eqid
    #
    facth1
    mpbird
    wph
    @3
    @13
    @15
    @51
    @52
    wb
    @12
    fta1g.2
    @40
    cB
    @14
    @50
    cP
    @0
    cR
    @43
    cF
    cG
    fta1g.p
    @53
    fta1g.b
    @39
    @43
    eqid
    #
    @41
    dvdsq1p
    syl3anc
    mpbid
    #
    eqcomd
    wph
    cP
    crg
    wcel
    #
    cG
    cB
    wcel
    #
    @45
    c.0
    wceq
    wph
    cP
    ccrg
    wcel
    #
    @56
    wph
    @9
    @58
    @22
    cP
    cR
    fta1g.p
    ply1crng
    syl
    #
    cP
    crngring
    syl
    wph
    @17
    @57
    @38
    cB
    cP
    cR
    cG
    @16
    fta1g.p
    fta1g.b
    @36
    mon1pcl
    syl
    #
    cB
    cP
    @43
    cG
    c.0
    fta1g.b
    @54
    fta1g.z
    ringlz
    syl2anc
    3netr4d
    @1
    c.0
    @44
    @45
    @1
    c.0
    cG
    @43
    oveq1
    necon3i
    syl
    #
    cB
    cD
    cP
    cR
    @1
    c.0
    fta1g.d
    fta1g.p
    fta1g.z
    fta1g.b
    deg1nn0cl
    syl3anc
    nn0cnd
    wph
    cN
    fta1glem.3
    nn0cnd
    #
    wph
    @49
    @18
    @2
    caddc
    co
    #
    c1
    cN
    caddc
    co
    #
    c1
    @2
    caddc
    co
    wph
    @47
    cG
    @1
    @43
    co
    #
    cD
    cfv
    @49
    @63
    wph
    cF
    @65
    cD
    wph
    cF
    @44
    @65
    @55
    wph
    @58
    @4
    @57
    @44
    @65
    wceq
    @59
    @42
    @60
    cB
    cP
    @43
    @1
    cG
    fta1g.b
    @54
    crngcom
    syl3anc
    eqtrd
    fveq2d
    fta1glem.4
    wph
    cB
    cD
    cP
    cR
    @43
    cR
    crlreg
    cfv
    #
    cG
    @1
    c.0
    fta1g.d
    fta1g.p
    @66
    eqid
    #
    fta1g.b
    @54
    fta1g.z
    @12
    @60
    wph
    cG
    c.0
    wne
    #
    @18
    cn0
    wcel
    #
    wph
    @18
    c1
    cn0
    wph
    @17
    @19
    @21
    @37
    simp2d
    #
    1nn0
    syl6eqel
    wph
    @3
    @57
    @68
    @69
    wb
    @12
    @60
    cB
    cD
    cP
    cR
    cG
    c.0
    fta1g.d
    fta1g.p
    fta1g.z
    fta1g.b
    deg1nn0clb
    syl2anc
    mpbird
    wph
    cR
    cui
    cfv
    #
    @66
    @18
    cG
    cco1
    cfv
    cfv
    #
    wph
    @3
    @71
    @66
    wss
    @12
    cR
    @71
    @66
    @67
    @71
    eqid
    #
    unitrrg
    syl
    wph
    @15
    @72
    @71
    wcel
    @40
    @14
    cD
    cR
    @71
    cG
    fta1g.d
    @73
    @39
    uc1pldg
    syl
    sseldd
    @42
    @61
    deg1mul2
    3eqtr3d
    wph
    cN
    cc
    wcel
    c1
    cc
    wcel
    @49
    @64
    wceq
    @62
    ax-1cn
    cN
    c1
    addcom
    sylancl
    wph
    @18
    c1
    @2
    caddc
    @70
    oveq1d
    3eqtr3rd
    addcanad
end
