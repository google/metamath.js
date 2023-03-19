include "ciin.mm"
include "wcel.mm"
include "wn.mm"
include "wral.mm"
include "wb.mm"
include "cvv.mm"
include "nvel.mm"
include "eqneltri.mm"
include "c0.mm"
include "ral0.mm"
include "raleqi.mm"
include "mpbir.mm"
include "wa.mm"
include "wo.mm"
include "pm3.22.mm"
include "olcd.mm"
include "xor.mm"
include "sylibr.mm"
include "mp2an.mm"

theorem eliincex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume eliinct.1: |- A = _V
  assume eliinct.2: |- B = (/)

  disjoint A x
  disjoint B x
  assert |- -. ( A e. |^|_ x e. B C <-> A. x e. B A e. C )

  proof
    cA
    vx
    cB
    cC
    ciin
    #
    wcel
    #
    wn
    #
    cA
    cC
    wcel
    #
    vx
    cB
    wral
    #
    @1
    @4
    wb
    wn
    #
    cA
    cvv
    @0
    eliinct.1
    @0
    nvel
    eqneltri
    @4
    @3
    vx
    c0
    wral
    @3
    vx
    ral0
    @3
    vx
    cB
    c0
    eliinct.2
    raleqi
    mpbir
    @2
    @4
    wa
    #
    @1
    @4
    wn
    wa
    #
    @4
    @2
    wa
    #
    wo
    @5
    @6
    @8
    @7
    @2
    @4
    pm3.22
    olcd
    @1
    @4
    xor
    sylibr
    mp2an
end
