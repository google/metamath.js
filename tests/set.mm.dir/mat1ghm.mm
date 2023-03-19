include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqid.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "adantr.mm"
include "csn.mm"
include "cfn.mm"
include "snfi.mm"
include "simpl.mm"
include "matgrp.mm"
include "sylancr.mm"
include "mat1f.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "simpr.mm"
include "adantl.mm"
include "mat1rhmelval.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "mat1rhmcl.mm"
include "snidg.mm"
include "jca.mm"
include "matplusgcell.mm"
include "syl21anc.mm"
include "ringacl.mm"
include "3eqtr4rd.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "2ralsng.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "matring.mm"
include "eqmat.mm"
include "isghmd.mm"

theorem mat1ghm
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vw: setvar w
  let vy: setvar y
  assume mat1rhmval.k: |- K = ( Base ` R )
  assume mat1rhmval.a: |- A = ( { E } Mat R )
  assume mat1rhmval.b: |- B = ( Base ` A )
  assume mat1rhmval.o: |- O = <. E , E >.
  assume mat1rhmval.f: |- F = ( x e. K |-> { <. O , x >. } )

  disjoint K x
  disjoint O x
  disjoint E x
  disjoint R x
  disjoint V x
  disjoint B x
  disjoint A x
  disjoint F x
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
  assert |- ( ( R e. Ring /\ E e. V ) -> F e. ( R GrpHom A ) )

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
    vw
    vy
    cR
    cplusg
    cfv
    #
    cA
    cplusg
    cfv
    #
    cR
    cA
    cF
    cK
    cB
    mat1rhmval.k
    mat1rhmval.b
    @3
    eqid
    #
    @4
    eqid
    #
    @0
    cR
    cgrp
    wcel
    @1
    cR
    ringgrp
    adantr
    @2
    cE
    csn
    #
    cfn
    wcel
    #
    @0
    cA
    cgrp
    wcel
    cE
    snfi
    #
    @0
    @1
    simpl
    #
    cA
    cR
    @7
    mat1rhmval.a
    matgrp
    sylancr
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
    vw
    cv
    #
    cK
    wcel
    #
    vy
    cv
    #
    cK
    wcel
    #
    wa
    #
    wa
    #
    @11
    @13
    @3
    co
    #
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    @13
    cF
    cfv
    #
    @4
    co
    #
    wceq
    #
    vi
    cv
    #
    vj
    cv
    #
    @18
    co
    #
    @23
    @24
    @21
    co
    #
    wceq
    #
    vj
    @7
    wral
    vi
    @7
    wral
    #
    @16
    @28
    cE
    cE
    @18
    co
    #
    cE
    cE
    @21
    co
    #
    wceq
    #
    @16
    cE
    cE
    @19
    co
    #
    cE
    cE
    @20
    co
    #
    @3
    co
    #
    @17
    @30
    @29
    @16
    @32
    @11
    @33
    @13
    @3
    @16
    @0
    @1
    @12
    @32
    @11
    wceq
    @2
    @0
    @15
    @10
    adantr
    #
    @2
    @1
    @15
    @0
    @1
    simpr
    #
    adantr
    #
    @15
    @12
    @2
    @12
    @14
    simpl
    adantl
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
    @11
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmelval
    syl3anc
    @16
    @0
    @1
    @14
    @33
    @13
    wceq
    @35
    @37
    @15
    @14
    @2
    @12
    @14
    simpr
    adantl
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
    @13
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmelval
    syl3anc
    oveq12d
    @16
    @19
    cB
    wcel
    #
    @20
    cB
    wcel
    #
    cE
    @7
    wcel
    #
    @42
    wa
    #
    @30
    @34
    wceq
    @16
    @0
    @1
    @12
    @40
    @35
    @37
    @38
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @11
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmcl
    syl3anc
    #
    @16
    @0
    @1
    @14
    @41
    @35
    @37
    @39
    vx
    cA
    cB
    cR
    cE
    cF
    cK
    cO
    cV
    @13
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmcl
    syl3anc
    #
    @2
    @43
    @15
    @1
    @43
    @0
    @1
    @42
    @42
    cE
    cV
    snidg
    #
    @46
    jca
    adantl
    adantr
    cA
    cB
    @3
    @4
    cR
    cE
    cE
    @7
    @19
    @20
    mat1rhmval.a
    mat1rhmval.b
    @6
    @5
    matplusgcell
    syl21anc
    @16
    @0
    @1
    @17
    cK
    wcel
    #
    @29
    @17
    wceq
    @35
    @37
    @16
    @0
    @12
    @14
    @47
    @35
    @38
    @39
    cK
    @3
    cR
    @11
    @13
    mat1rhmval.k
    @5
    ringacl
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
    @17
    mat1rhmval.k
    mat1rhmval.a
    mat1rhmval.b
    mat1rhmval.o
    mat1rhmval.f
    mat1rhmelval
    syl3anc
    3eqtr4rd
    @2
    @28
    @31
    wb
    #
    @15
    @2
    @1
    @1
    @49
    @36
    @36
    @27
    cE
    @24
    @18
    co
    #
    cE
    @24
    @21
    co
    #
    wceq
    @31
    vi
    vj
    cE
    cE
    cV
    cV
    @23
    cE
    wceq
    @25
    @50
    @26
    @51
    @23
    cE
    @24
    @18
    oveq1
    @23
    cE
    @24
    @21
    oveq1
    eqeq12d
    @24
    cE
    wceq
    @50
    @29
    @51
    @30
    @24
    cE
    cE
    @18
    oveq2
    @24
    cE
    cE
    @21
    oveq2
    eqeq12d
    2ralsng
    syl2anc
    adantr
    mpbird
    @16
    @18
    cB
    wcel
    #
    @21
    cB
    wcel
    #
    @22
    @28
    wb
    @16
    @0
    @1
    @47
    @52
    @35
    @37
    @48
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
    mat1rhmcl
    syl3anc
    @16
    cA
    crg
    wcel
    #
    @40
    @41
    @53
    @2
    @54
    @15
    @2
    @8
    @0
    @54
    @9
    @10
    cA
    cR
    @7
    mat1rhmval.a
    matring
    sylancr
    adantr
    @44
    @45
    cB
    @4
    cA
    @19
    @20
    mat1rhmval.b
    @6
    ringacl
    syl3anc
    cA
    cB
    cR
    vi
    vj
    @7
    @18
    @21
    mat1rhmval.a
    mat1rhmval.b
    eqmat
    syl2anc
    mpbird
    isghmd
end
