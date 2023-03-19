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
include "cress.mm"
include "cin.mm"
include "dmatALTval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabexg.mm"
include "mp1i.mm"
include "eqid.mm"
include "ressbas.mm"
include "syl.mm"
include "inrab2.mm"
include "inidm.mm"
include "rabeq.mm"
include "syl5eq.mm"
include "3eqtr2d.mm"

theorem dmatALTbas
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let cN: class N
  let c.0: class .0.
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume dmatALTval.a: |- A = ( N Mat R )
  assume dmatALTval.b: |- B = ( Base ` A )
  assume dmatALTval.0: |- .0. = ( 0g ` R )
  assume dmatALTval.d: |- D = ( N DMatALT R )

  disjoint B m
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint i j
  disjoint i m
  disjoint j m
  disjoint R i
  disjoint R j
  disjoint R m
  disjoint A n
  disjoint A r
  disjoint n r
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint N a
  disjoint N n
  disjoint N r
  disjoint a i
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint i n
  disjoint i r
  disjoint j n
  disjoint j r
  disjoint R a
  disjoint R n
  disjoint R r
  disjoint .0. n
  disjoint .0. r
  disjoint k x
  assert |- ( ( N e. Fin /\ R e. _V ) -> ( Base ` D ) = { m e. B | A. i e. N A. j e. N ( i =/= j -> ( i m j ) = .0. ) } )

  proof
    cN
    cfn
    wcel
    cR
    cvv
    wcel
    wa
    #
    cD
    cbs
    cfv
    cA
    vi
    cv
    #
    vj
    cv
    #
    wne
    @1
    @2
    vm
    cv
    co
    c.0
    wceq
    wi
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
    cress
    co
    #
    cbs
    cfv
    #
    @4
    cB
    cin
    #
    @4
    @0
    cD
    @5
    cbs
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
    dmatALTval
    fveq2d
    @0
    @4
    cvv
    wcel
    #
    @7
    @6
    wceq
    cB
    cvv
    wcel
    @8
    @0
    cB
    cA
    cbs
    cfv
    cvv
    dmatALTval.b
    cA
    cbs
    fvex
    eqeltri
    @3
    vm
    cB
    cvv
    rabexg
    mp1i
    @4
    cB
    @5
    cvv
    cA
    @5
    eqid
    dmatALTval.b
    ressbas
    syl
    @0
    @7
    @3
    vm
    cB
    cB
    cin
    #
    crab
    #
    @4
    @3
    vm
    cB
    cB
    inrab2
    @9
    cB
    wceq
    @10
    @4
    wceq
    @0
    cB
    inidm
    @3
    vm
    @9
    cB
    rabeq
    mp1i
    syl5eq
    3eqtr2d
end
