include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "dmatval.mm"
include "eleq2d.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem dmatel
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume dmatval.a: |- A = ( N Mat R )
  assume dmatval.b: |- B = ( Base ` A )
  assume dmatval.0: |- .0. = ( 0g ` R )
  assume dmatval.d: |- D = ( N DMat R )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint M i
  disjoint M j
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint V n
  disjoint V r
  disjoint .0. n
  disjoint .0. r
  disjoint M m
  disjoint .0. m
  assert |- ( ( N e. Fin /\ R e. V ) -> ( M e. D <-> ( M e. B /\ A. i e. N A. j e. N ( i =/= j -> ( i M j ) = .0. ) ) ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    wa
    #
    cM
    cD
    wcel
    cM
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @1
    @2
    vm
    cv
    #
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    vm
    cB
    crab
    #
    wcel
    cM
    cB
    wcel
    @3
    @1
    @2
    cM
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wa
    @0
    cD
    @9
    cM
    cA
    cB
    cD
    cR
    vi
    vj
    vm
    cN
    cV
    c.0
    dmatval.a
    dmatval.b
    dmatval.0
    dmatval.d
    dmatval
    eleq2d
    @8
    @13
    vm
    cM
    cB
    @4
    cM
    wceq
    #
    @7
    @12
    vi
    vj
    cN
    cN
    @14
    @6
    @11
    @3
    @14
    @5
    @10
    c.0
    @1
    @2
    @4
    cM
    oveq
    eqeq1d
    imbi2d
    2ralbidv
    elrab
    syl6bb
end
