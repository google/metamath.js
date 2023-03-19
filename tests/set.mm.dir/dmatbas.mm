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
include "cdmatalt.mm"
include "cbs.mm"
include "cfv.mm"
include "dmatval.mm"
include "cvv.mm"
include "elex.mm"
include "eqid.mm"
include "dmatALTbas.mm"
include "sylan2.mm"
include "eqtr4d.mm"

theorem dmatbas
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume dmatbas.a: |- A = ( N Mat R )
  assume dmatbas.b: |- B = ( Base ` A )
  assume dmatbas.0: |- .0. = ( 0g ` R )
  assume dmatbas.d: |- D = ( N DMat R )


  assert |- ( ( N e. Fin /\ R e. V ) -> D = ( Base ` ( N DMatALT R ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    cD
    vi
    cv
    #
    vj
    cv
    #
    wne
    @2
    @3
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
    vm
    cB
    crab
    #
    cN
    cR
    cdmatalt
    co
    #
    cbs
    cfv
    #
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
    dmatbas.a
    dmatbas.b
    dmatbas.0
    dmatbas.d
    dmatval
    @1
    @0
    cR
    cvv
    wcel
    @6
    @4
    wceq
    cR
    cV
    elex
    cA
    cB
    @5
    cR
    vi
    vj
    vm
    cN
    c.0
    dmatbas.a
    dmatbas.b
    dmatbas.0
    @5
    eqid
    dmatALTbas
    sylan2
    eqtr4d
end
