include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cmnd.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cur.mm"
include "w3a.mm"
include "cmhm.mm"
include "ringmgp.mm"
include "adantl.mm"
include "csubrg.mm"
include "c0g.mm"
include "eqid.mm"
include "scmatsrng.mm"
include "subrgring.mm"
include "3syl.mm"
include "scmatf.mm"
include "scmatstrbas.mm"
include "feq3d.mm"
include "mpbird.mm"
include "scmatscmiddistr.mm"
include "ressmulr.mm"
include "syl.mm"
include "adantr.mm"
include "oveqd.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "ringcl.mm"
include "scmatrhmval.mm"
include "syl2anc.mm"
include "ad2ant2lr.mm"
include "ad2ant2l.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "ringidcl.mm"
include "csca.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "clmod.mm"
include "matlmod.mm"
include "matring.mm"
include "lmodvs1.mm"
include "eqtrd.mm"
include "subrg1.mm"
include "3jca.mm"
include "jca31.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ringidval.mm"
include "ismhm.mm"

theorem scmatmhm
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let c.1: class .1.
  let cF: class F
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cX: class X
  let vc: setvar c
  let vi: setvar i
  let vj: setvar j
  assume scmatrhmval.k: |- K = ( Base ` R )
  assume scmatrhmval.a: |- A = ( N Mat R )
  assume scmatrhmval.o: |- .1. = ( 1r ` A )
  assume scmatrhmval.t: |- .* = ( .s ` A )
  assume scmatrhmval.f: |- F = ( x e. K |-> ( x .* .1. ) )
  assume scmatrhmval.c: |- C = ( N ScMat R )
  assume scmatghm.s: |- S = ( A |`s C )
  assume scmatmhm.m: |- M = ( mulGrp ` R )
  assume scmatmhm.t: |- T = ( mulGrp ` S )

  disjoint K x
  disjoint R x
  disjoint .1. x
  disjoint .* x
  disjoint C x
  disjoint N x
  disjoint M y
  disjoint M z
  disjoint y z
  disjoint T y
  disjoint T z
  disjoint V x
  disjoint X x
  disjoint K c
  disjoint N c
  disjoint R c
  disjoint X c
  disjoint .* c
  disjoint .1. c
  disjoint C c
  disjoint C y
  disjoint c y
  disjoint F c
  disjoint F y
  disjoint K y
  disjoint N y
  disjoint c x
  disjoint x y
  disjoint R y
  disjoint F z
  disjoint K i
  disjoint K j
  disjoint K z
  disjoint i j
  disjoint i z
  disjoint j z
  disjoint N i
  disjoint N j
  disjoint N z
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint x z
  disjoint y z
  disjoint R i
  disjoint R j
  disjoint R z
  disjoint .1. i
  disjoint .1. j
  disjoint .* i
  disjoint .* j
  disjoint S y
  disjoint S z
  assert |- ( ( N e. Fin /\ R e. Ring ) -> F e. ( M MndHom T ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cM
    cmnd
    wcel
    #
    cT
    cmnd
    wcel
    #
    wa
    cK
    cS
    cbs
    cfv
    #
    cF
    wf
    #
    vy
    cv
    #
    vz
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
    @7
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    wceq
    #
    vz
    cK
    wral
    vy
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
    cS
    cur
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    cF
    cM
    cT
    cmhm
    co
    wcel
    @2
    @3
    @4
    @22
    @1
    @3
    @0
    cR
    cM
    scmatmhm.m
    ringmgp
    adantl
    @2
    cC
    cA
    csubrg
    cfv
    #
    wcel
    #
    cS
    crg
    wcel
    @4
    cA
    cA
    cbs
    cfv
    #
    cR
    cC
    cK
    cN
    cR
    c0g
    cfv
    #
    scmatrhmval.a
    @25
    eqid
    #
    scmatrhmval.k
    @26
    eqid
    #
    scmatrhmval.c
    scmatsrng
    #
    cC
    cA
    cS
    scmatghm.s
    subrgring
    cS
    cT
    scmatmhm.t
    ringmgp
    3syl
    @2
    @6
    @17
    @21
    @2
    @6
    cK
    cC
    cF
    wf
    vx
    cA
    cC
    cR
    c.1
    cF
    c.as
    cK
    cN
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval.c
    scmatf
    @2
    @5
    cC
    cF
    cK
    cA
    cC
    cR
    cS
    cN
    scmatrhmval.a
    scmatrhmval.c
    scmatghm.s
    scmatstrbas
    feq3d
    mpbird
    @2
    @16
    vy
    vz
    cK
    cK
    @2
    @7
    cK
    wcel
    #
    @8
    cK
    wcel
    #
    wa
    #
    wa
    #
    @10
    c.1
    c.as
    co
    #
    @7
    c.1
    c.as
    co
    #
    @8
    c.1
    c.as
    co
    #
    @14
    co
    #
    @11
    @15
    @33
    @35
    @36
    cA
    cmulr
    cfv
    #
    co
    @34
    @37
    cA
    cK
    cR
    @7
    @8
    @9
    @38
    c.1
    c.as
    cN
    @26
    scmatrhmval.a
    scmatrhmval.k
    @28
    scmatrhmval.o
    scmatrhmval.t
    @9
    eqid
    #
    @38
    eqid
    #
    scmatscmiddistr
    @33
    @38
    @14
    @35
    @36
    @2
    @38
    @14
    wceq
    #
    @32
    @2
    @24
    @41
    @29
    cC
    cA
    cS
    @38
    @23
    scmatghm.s
    @40
    ressmulr
    syl
    adantr
    oveqd
    eqtr3d
    @33
    @1
    @10
    cK
    wcel
    #
    @11
    @34
    wceq
    @2
    @1
    @32
    @0
    @1
    simpr
    #
    adantr
    @33
    @1
    @30
    @31
    w3a
    #
    @42
    @33
    @1
    @32
    wa
    @44
    @2
    @1
    @32
    @43
    anim1i
    @1
    @30
    @31
    3anass
    sylibr
    cK
    cR
    @9
    @7
    @8
    scmatrhmval.k
    @39
    ringcl
    syl
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @10
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    syl2anc
    @33
    @12
    @35
    @13
    @36
    @14
    @1
    @30
    @12
    @35
    wceq
    @0
    @31
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @7
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    ad2ant2lr
    @1
    @31
    @13
    @36
    wceq
    @0
    @30
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @8
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    ad2ant2l
    oveq12d
    3eqtr4d
    ralrimivva
    @2
    @19
    c.1
    @20
    @2
    @19
    @18
    c.1
    c.as
    co
    #
    c.1
    @2
    @1
    @18
    cK
    wcel
    #
    @19
    @45
    wceq
    @43
    @1
    @46
    @0
    cK
    cR
    @18
    scmatrhmval.k
    @18
    eqid
    #
    ringidcl
    adantl
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @18
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    syl2anc
    @2
    @45
    cA
    csca
    cfv
    #
    cur
    cfv
    #
    c.1
    c.as
    co
    #
    c.1
    @2
    @18
    @49
    c.1
    c.as
    @2
    cR
    @48
    cur
    cA
    cR
    cN
    crg
    scmatrhmval.a
    matsca2
    fveq2d
    oveq1d
    @2
    cA
    clmod
    wcel
    c.1
    @25
    wcel
    #
    @50
    c.1
    wceq
    cA
    cR
    cN
    scmatrhmval.a
    matlmod
    @2
    cA
    crg
    wcel
    @51
    cA
    cR
    cN
    scmatrhmval.a
    matring
    @25
    cA
    c.1
    @27
    scmatrhmval.o
    ringidcl
    syl
    c.as
    @49
    @48
    @25
    cA
    c.1
    @27
    @48
    eqid
    scmatrhmval.t
    @49
    eqid
    lmodvs1
    syl2anc
    eqtrd
    eqtrd
    @2
    @24
    c.1
    @20
    wceq
    @29
    cC
    cA
    cS
    c.1
    scmatghm.s
    scmatrhmval.o
    subrg1
    syl
    eqtrd
    3jca
    jca31
    vy
    vz
    cK
    @5
    @9
    @14
    cM
    cT
    cF
    @20
    @18
    cK
    cR
    cM
    scmatmhm.m
    scmatrhmval.k
    mgpbas
    @5
    cS
    cT
    scmatmhm.t
    @5
    eqid
    mgpbas
    cR
    @9
    cM
    scmatmhm.m
    @39
    mgpplusg
    cS
    @14
    cT
    scmatmhm.t
    @14
    eqid
    mgpplusg
    cR
    @18
    cM
    scmatmhm.m
    @47
    ringidval
    cS
    @20
    cT
    scmatmhm.t
    @20
    eqid
    ringidval
    ismhm
    sylibr
end
