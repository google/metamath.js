include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cfv.mm"
include "chash.mm"
include "cmgp.mm"
include "cmg.mm"
include "co.mm"
include "cbs.mm"
include "cv.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "wceq.mm"
include "wral.mm"
include "id.mm"
include "crg.mm"
include "crngring.mm"
include "anim1i.mm"
include "ancomd.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "3syl.mm"
include "syl.mm"
include "adantr.mm"
include "jca32.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "mat1ov.mm"
include "ralrimivva.mm"
include "mdetdiagid.mm"
include "sylc.mm"
include "csrg.mm"
include "cn0.mm"
include "ringsrg.mm"
include "hashcl.mm"
include "srg1expzeq1.mm"
include "syl2an.mm"
include "eqtrd.mm"

theorem mdet1
  let cA: class A
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume mdet1.d: |- D = ( N maDet R )
  assume mdet1.a: |- A = ( N Mat R )
  assume mdet1.n: |- I = ( 1r ` A )
  assume mdet1.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. CRing /\ N e. Fin ) -> ( D ` I ) = .1. )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cI
    cD
    cfv
    #
    cN
    chash
    cfv
    #
    c.1
    cR
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    c.1
    @2
    @2
    cI
    cA
    cbs
    cfv
    #
    wcel
    #
    c.1
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    wa
    vi
    cv
    #
    vj
    cv
    #
    cI
    co
    vi
    vj
    weq
    c.1
    cR
    c0g
    cfv
    #
    cif
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    @3
    @7
    wceq
    @2
    @2
    @9
    @11
    @2
    id
    @2
    @1
    cR
    crg
    wcel
    #
    wa
    cA
    crg
    wcel
    @9
    @2
    @16
    @1
    @0
    @16
    @1
    cR
    crngring
    #
    anim1i
    ancomd
    cA
    cR
    cN
    mdet1.a
    matring
    @8
    cA
    cI
    @8
    eqid
    #
    mdet1.n
    ringidcl
    3syl
    @0
    @11
    @1
    @0
    @16
    @11
    @17
    @10
    cR
    c.1
    @10
    eqid
    #
    mdet1.o
    ringidcl
    syl
    adantr
    jca32
    @2
    @15
    vi
    vj
    cN
    cN
    @2
    @12
    cN
    wcel
    #
    @13
    cN
    wcel
    #
    wa
    #
    wa
    cA
    cR
    cI
    c.1
    @12
    @13
    cN
    @14
    mdet1.a
    mdet1.o
    @14
    eqid
    #
    @0
    @1
    @22
    simplr
    @2
    @16
    @22
    @0
    @16
    @1
    @17
    adantr
    adantr
    @2
    @20
    @21
    simprl
    @2
    @20
    @21
    simprr
    mdet1.n
    mat1ov
    ralrimivva
    cA
    @8
    @10
    cD
    cR
    @6
    vi
    vj
    @5
    cI
    cN
    c.1
    @14
    mdet1.d
    mdet1.a
    @18
    @5
    eqid
    #
    @23
    @19
    @6
    eqid
    #
    mdetdiagid
    sylc
    @0
    cR
    csrg
    wcel
    #
    @4
    cn0
    wcel
    @7
    c.1
    wceq
    @1
    @0
    @16
    @26
    @17
    cR
    ringsrg
    syl
    cN
    hashcl
    cR
    @6
    c.1
    @5
    @4
    @24
    @25
    mdet1.o
    srg1expzeq1
    syl2an
    eqtrd
end
