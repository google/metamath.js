include "cfn.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "dmatALTbas.mm"
include "eleq2d.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem dmatALTbasel
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vn: setvar n
  let vr: setvar r
  let vm: setvar m
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume dmatALTval.a: |- A = ( N Mat R )
  assume dmatALTval.b: |- B = ( Base ` A )
  assume dmatALTval.0: |- .0. = ( 0g ` R )
  assume dmatALTval.d: |- D = ( N DMatALT R )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint M i
  disjoint M j
  disjoint A n
  disjoint A r
  disjoint n r
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint N a
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint a i
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint R a
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint .0. n
  disjoint .0. r
  disjoint M m
  disjoint .0. m
  disjoint k x
  assert |- ( ( N e. Fin /\ R e. _V ) -> ( M e. ( Base ` D ) <-> ( M e. B /\ A. i e. N A. j e. N ( i =/= j -> ( i M j ) = .0. ) ) ) )

  proof
    cN
    cfn
    wcel
    cR
    cvv
    wcel
    wa
    #
    cM
    cD
    cbs
    cfv
    #
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
    @2
    @3
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
    @4
    @2
    @3
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
    @1
    @10
    cM
    cA
    cB
    cD
    cR
    vi
    vj
    vm
    cN
    c.0
    dmatALTval.a
    dmatALTval.b
    dmatALTval.0
    dmatALTval.d
    dmatALTbas
    eleq2d
    @9
    @14
    vm
    cM
    cB
    @5
    cM
    wceq
    #
    @8
    @13
    vi
    vj
    cN
    cN
    @15
    @7
    @12
    @4
    @15
    @6
    @11
    c.0
    @2
    @3
    @5
    cM
    oveq
    eqeq1d
    imbi2d
    2ralbidv
    elrab
    syl6bb
end
