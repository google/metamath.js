include "wcel.mm"
include "w3a.mm"
include "weq.mm"
include "cif.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "maduval.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "simp1r.mm"
include "eqeq2d.mm"
include "simp1l.mm"
include "ifbid.mm"
include "ifbieq1d.mm"
include "mpt2eq3dva.mm"
include "fveq2d.mm"
include "adantl.mm"
include "simp2.mm"
include "simp3.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem maducoeval
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let vk: setvar k
  let cH: class H
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  let vn: setvar n
  let vr: setvar r
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  assume madufval.a: |- A = ( N Mat R )
  assume madufval.d: |- D = ( N maDet R )
  assume madufval.j: |- J = ( N maAdju R )
  assume madufval.b: |- B = ( Base ` A )
  assume madufval.o: |- .1. = ( 1r ` R )
  assume madufval.z: |- .0. = ( 0g ` R )

  disjoint N k
  disjoint N l
  disjoint k l
  disjoint R k
  disjoint R l
  disjoint M k
  disjoint M l
  disjoint I k
  disjoint I l
  disjoint H k
  disjoint H l
  disjoint N n
  disjoint N r
  disjoint N m
  disjoint N i
  disjoint N j
  disjoint n r
  disjoint m n
  disjoint i n
  disjoint j n
  disjoint k n
  disjoint l n
  disjoint m r
  disjoint i r
  disjoint j r
  disjoint k r
  disjoint l r
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint l m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint R n
  disjoint R r
  disjoint R m
  disjoint R i
  disjoint R j
  disjoint B m
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint D m
  disjoint .1. m
  disjoint .0. m
  disjoint B i
  disjoint B j
  disjoint I i
  disjoint I j
  disjoint D i
  disjoint D j
  disjoint .1. i
  disjoint .1. j
  disjoint .0. i
  disjoint .0. j
  disjoint H i
  disjoint H j
  assert |- ( ( M e. B /\ I e. N /\ H e. N ) -> ( I ( J ` M ) H ) = ( D ` ( k e. N , l e. N |-> if ( k = H , if ( l = I , .1. , .0. ) , ( k M l ) ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cI
    cN
    wcel
    #
    cH
    cN
    wcel
    #
    w3a
    #
    vi
    vj
    cI
    cH
    cN
    cN
    vk
    vl
    cN
    cN
    vk
    vj
    weq
    #
    vl
    vi
    weq
    #
    c.1
    c.0
    cif
    #
    vk
    cv
    #
    vl
    cv
    #
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    vk
    vl
    cN
    cN
    @7
    cH
    wceq
    #
    @8
    cI
    wceq
    #
    c.1
    c.0
    cif
    #
    @9
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    cM
    cJ
    cfv
    #
    cvv
    @0
    @1
    @19
    vi
    vj
    cN
    cN
    @12
    cmpt2
    wceq
    @2
    cA
    cB
    cD
    cR
    c.1
    vi
    vj
    vk
    cJ
    cM
    cN
    c.0
    vl
    madufval.a
    madufval.d
    madufval.j
    madufval.b
    madufval.o
    madufval.z
    maduval
    3ad2ant1
    vi
    cv
    #
    cI
    wceq
    #
    vj
    cv
    #
    cH
    wceq
    #
    wa
    #
    @12
    @18
    wceq
    @3
    @24
    @11
    @17
    cD
    @24
    vk
    vl
    cN
    cN
    @10
    @16
    @24
    @7
    cN
    wcel
    #
    @8
    cN
    wcel
    #
    w3a
    #
    @4
    @13
    @6
    @15
    @9
    @27
    @22
    cH
    @7
    @21
    @23
    @25
    @26
    simp1r
    eqeq2d
    @27
    @5
    @14
    c.1
    c.0
    @27
    @20
    cI
    @8
    @21
    @23
    @25
    @26
    simp1l
    eqeq2d
    ifbid
    ifbieq1d
    mpt2eq3dva
    fveq2d
    adantl
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    @17
    cD
    fvexd
    ovmpt2d
end
