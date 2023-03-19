include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "dmatel.mm"
include "simpl.mm"
include "syl6bi.mm"

theorem dmatmat
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cM: class M
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vi: setvar i
  let vj: setvar j
  assume dmatval.a: |- A = ( N Mat R )
  assume dmatval.b: |- B = ( Base ` A )
  assume dmatval.0: |- .0. = ( 0g ` R )
  assume dmatval.d: |- D = ( N DMat R )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( M e. D -> M e. B ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    wa
    cM
    cD
    wcel
    cM
    cB
    wcel
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    @1
    @2
    cM
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
    wa
    @0
    cA
    cB
    cD
    cR
    vi
    vj
    cM
    cN
    cV
    c.0
    dmatval.a
    dmatval.b
    dmatval.0
    dmatval.d
    dmatel
    @0
    @3
    simpl
    syl6bi
end
