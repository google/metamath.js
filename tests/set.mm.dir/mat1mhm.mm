include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cmnd.mm"
include "wf.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cur.mm"
include "w3a.mm"
include "cmhm.mm"
include "ringmgp.mm"
include "adantr.mm"
include "csn.mm"
include "cfn.mm"
include "snfi.mm"
include "simpl.mm"
include "matring.mm"
include "sylancr.mm"
include "syl.mm"
include "jca.mm"
include "mat1f.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ringmnd.mm"
include "simpr.mm"
include "simpll.mm"
include "cbs.mm"
include "eqid.mm"
include "snidg.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "mat1rhmcl.mm"
include "syl3anc.mm"
include "matecld.mm"
include "simprr.mm"
include "ringcl.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "adantl.mm"
include "gsumsnd.mm"
include "mat1rhmelval.mm"
include "eqtrd.mm"
include "matmulcell.mm"
include "3eqtr4rd.mm"
include "wb.mm"
include "eqeq12d.mm"
include "2ralsng.mm"
include "sylancom.mm"
include "mpbird.mm"
include "eqmat.mm"
include "syl2anc.mm"
include "ralrimivva.mm"
include "cop.mm"
include "ringidcl.mm"
include "mat1rhmval.mm"
include "mpd3an3.mm"
include "mat1dimid.mm"
include "eqtr4d.mm"
include "3jca.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ringidval.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem mat1mhm
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let ve: setvar e
  let vw: setvar w
  let vy: setvar y
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  assume mat1rhmval.k: |- K = ( Base ` R )
  assume mat1rhmval.a: |- A = ( { E } Mat R )
  assume mat1rhmval.b: |- B = ( Base ` A )
  assume mat1rhmval.o: |- O = <. E , E >.
  assume mat1rhmval.f: |- F = ( x e. K |-> { <. O , x >. } )
  assume mat1mhm.m: |- M = ( mulGrp ` R )
  assume mat1mhm.n: |- N = ( mulGrp ` A )

  disjoint F x
  disjoint M x
  disjoint N x
  disjoint K x
  disjoint O x
  disjoint E x
  disjoint R x
  disjoint V x
  disjoint B x
  disjoint A x
  disjoint F x
  disjoint B e
  disjoint B w
  disjoint e w
  disjoint E e
  disjoint F e
  disjoint F y
  disjoint e x
  disjoint e y
  disjoint x y
  disjoint K e
  disjoint M w
  disjoint M y
  disjoint w x
  disjoint w y
  disjoint N w
  disjoint N y
  disjoint R e
  disjoint V e
  disjoint X x
  disjoint A i
  disjoint A j
  disjoint A w
  disjoint A y
  disjoint i j
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint B w
  disjoint B y
  disjoint E i
  disjoint E j
  disjoint E w
  disjoint E y
  disjoint F i
  disjoint F j
  disjoint F w
  disjoint F y
  disjoint K w
  disjoint K y
  disjoint R i
  disjoint R j
  disjoint R w
  disjoint R y
  disjoint V w
  disjoint V y
  assert |- ( ( R e. Ring /\ E e. V ) -> F e. ( M MndHom N ) )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    wa
    #
    cM
    cmnd
    wcel
    #
    cN
    cmnd
    wcel
    #
    wa
    cK
    cB
    cF
    wf
    #
    vw
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cA
    cmulr
    cfv
    #
    co
    #
    wceq
    #
    vy
    cK
    wral
    vw
    cK
    wral
    #
    cR
    cur
    cfv
    #
    cF
    cfv
    #
    cA
    cur
    cfv
    #
    wceq
    #
    w3a
    cF
    cM
    cN
    cmhm
    co
    wcel
    @2
    @3
    @4
    @0
    @3
    @1
    cR
    cM
    mat1mhm.m
    ringmgp
    adantr
    @2
    cA
    crg
    wcel
    #
    @4
    @2
    cE
    csn
    #
    cfn
    wcel
    @0
    @21
    cE
    snfi
    @0
    @1
    simpl
    cA
    cR
    @22
    mat1rhmval.a
    matring
    sylancr
    #
    cA
    cN
    mat1mhm.n
    ringmgp
    syl
    jca
    @2
    @5
    @16
    @20
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1f
    @2
    @15
    vw
    vy
    cK
    cK
    @2
    @6
    cK
    wcel
    #
    @7
    cK
    wcel
    #
    wa
    #
    wa
    #
    @15
    vi
    cv
    #
    vj
    cv
    #
    @10
    co
    #
    @28
    @29
    @14
    co
    #
    wceq
    #
    vj
    @22
    wral
    vi
    @22
    wral
    #
    @27
    @33
    cE
    cE
    @10
    co
    #
    cE
    cE
    @14
    co
    #
    wceq
    #
    @27
    cR
    ve
    @22
    cE
    ve
    cv
    #
    @11
    co
    #
    @37
    cE
    @12
    co
    #
    @8
    co
    #
    cmpt
    cgsu
    co
    #
    @9
    @35
    @34
    @27
    @41
    cE
    cE
    @11
    co
    #
    cE
    cE
    @12
    co
    #
    @8
    co
    #
    @9
    @27
    @40
    cK
    @44
    ve
    cR
    cE
    cV
    mat1rhmval.k
    @2
    cR
    cmnd
    wcel
    #
    @26
    @0
    @45
    @1
    cR
    ringmnd
    adantr
    adantr
    @2
    @1
    @26
    @0
    @1
    simpr
    #
    adantr
    #
    @27
    @0
    @42
    cK
    wcel
    @43
    cK
    wcel
    @44
    cK
    wcel
    @0
    @1
    @26
    simpll
    #
    @27
    cA
    cA
    cbs
    cfv
    #
    cR
    cE
    cE
    cK
    @11
    @22
    mat1rhmval.a
    mat1rhmval.k
    @49
    eqid
    #
    @1
    cE
    @22
    wcel
    #
    @0
    @26
    cE
    cV
    snidg
    #
    ad2antlr
    #
    @53
    @27
    @0
    @1
    @24
    @11
    @49
    wcel
    @48
    @47
    @2
    @24
    @25
    simprl
    #
    vx
    cA
    @49
    cR
    cE
    cF
    cK
    cO
    cV
    @6
    mat1rhmval.k
    mat1rhmval.a
    @50
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmcl
    syl3anc
    matecld
    @27
    cA
    @49
    cR
    cE
    cE
    cK
    @12
    @22
    mat1rhmval.a
    mat1rhmval.k
    @50
    @53
    @53
    @27
    @0
    @1
    @25
    @12
    @49
    wcel
    @48
    @47
    @2
    @24
    @25
    simprr
    #
    vx
    cA
    @49
    cR
    cE
    cF
    cK
    cO
    cV
    @7
    mat1rhmval.k
    mat1rhmval.a
    @50
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmcl
    syl3anc
    matecld
    cK
    cR
    @8
    @42
    @43
    mat1rhmval.k
    @8
    eqid
    #
    ringcl
    syl3anc
    @37
    cE
    wceq
    #
    @40
    @44
    wceq
    @27
    @57
    @38
    @42
    @39
    @43
    @8
    @37
    cE
    cE
    @11
    oveq2
    @37
    cE
    cE
    @12
    oveq1
    oveq12d
    adantl
    gsumsnd
    @27
    @42
    @6
    @43
    @7
    @8
    @27
    @0
    @1
    @24
    @42
    @6
    wceq
    @48
    @47
    @54
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @6
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmelval
    syl3anc
    @27
    @0
    @1
    @25
    @43
    @7
    wceq
    @48
    @47
    @55
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @7
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmelval
    syl3anc
    oveq12d
    eqtrd
    @27
    @0
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    wa
    @51
    @51
    wa
    #
    @35
    @41
    wceq
    @48
    @27
    @58
    @59
    @27
    @0
    @1
    @24
    @58
    @48
    @47
    @54
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @6
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmcl
    syl3anc
    #
    @27
    @0
    @1
    @25
    @59
    @48
    @47
    @55
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @7
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmcl
    syl3anc
    #
    jca
    @1
    @60
    @0
    @26
    @1
    @51
    @51
    @52
    @52
    jca
    ad2antlr
    cA
    cB
    cR
    @8
    @13
    ve
    cE
    cE
    @22
    @11
    @12
    mat1rhmval.a
    mat1rhmval.b
    @56
    @13
    eqid
    #
    matmulcell
    syl3anc
    @27
    @0
    @1
    @9
    cK
    wcel
    #
    @34
    @9
    wceq
    @48
    @47
    @27
    @0
    @24
    @25
    @64
    @48
    @54
    @55
    cK
    cR
    @8
    @6
    @7
    mat1rhmval.k
    @56
    ringcl
    syl3anc
    #
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @9
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmelval
    syl3anc
    3eqtr4rd
    @2
    @33
    @36
    wb
    #
    @26
    @0
    @1
    @1
    @66
    @46
    @32
    cE
    @29
    @10
    co
    #
    cE
    @29
    @14
    co
    #
    wceq
    @36
    vi
    vj
    cE
    cE
    cV
    cV
    @28
    cE
    wceq
    @30
    @67
    @31
    @68
    @28
    cE
    @29
    @10
    oveq1
    @28
    cE
    @29
    @14
    oveq1
    eqeq12d
    @29
    cE
    wceq
    @67
    @34
    @68
    @35
    @29
    cE
    cE
    @10
    oveq2
    @29
    cE
    cE
    @14
    oveq2
    eqeq12d
    2ralsng
    sylancom
    adantr
    mpbird
    @27
    @10
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    @15
    @33
    wb
    @27
    @0
    @1
    @64
    @69
    @48
    @47
    @65
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @9
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmcl
    syl3anc
    @27
    @21
    @58
    @59
    @70
    @2
    @21
    @26
    @23
    adantr
    @61
    @62
    cB
    cA
    @13
    @11
    @12
    mat1rhmval.b
    @63
    ringcl
    syl3anc
    cA
    cB
    cR
    vi
    vj
    @22
    @10
    @14
    mat1rhmval.a
    mat1rhmval.b
    eqmat
    syl2anc
    mpbird
    ralrimivva
    @2
    @18
    cO
    @17
    cop
    csn
    #
    @19
    @0
    @1
    @17
    cK
    wcel
    #
    @18
    @71
    wceq
    @0
    @72
    @1
    cK
    cR
    @17
    mat1rhmval.k
    @17
    eqid
    #
    ringidcl
    adantr
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @17
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmval
    mpd3an3
    cA
    cK
    cR
    cE
    cO
    cV
    mat1rhmval.a
    mat1rhmval.k
    mat1rhmval.o
    mat1dimid
    eqtr4d
    3jca
    vw
    vy
    cK
    cB
    @8
    @13
    cM
    cN
    cF
    @19
    @17
    cK
    cR
    cM
    mat1mhm.m
    mat1rhmval.k
    mgpbas
    cB
    cA
    cN
    mat1mhm.n
    mat1rhmval.b
    mgpbas
    cR
    @8
    cM
    mat1mhm.m
    @56
    mgpplusg
    cA
    @13
    cN
    mat1mhm.n
    @63
    mgpplusg
    cR
    @17
    cM
    mat1mhm.m
    @73
    ringidval
    cA
    @19
    cN
    mat1mhm.n
    @19
    eqid
    ringidval
    ismhm
    sylanbrc
end
