include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "caddc.mm"
include "wceq.mm"
include "elfznn0.mm"
include "nn0cnd.mm"
include "addcom.mm"
include "syl2an.mm"

theorem fz0addcom
  let cA: class A
  let cB: class B
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ( 0 ... N ) /\ B e. ( 0 ... N ) ) -> ( A + B ) = ( B + A ) )

  proof
    cA
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cB
    cA
    caddc
    co
    wceq
    cB
    @0
    wcel
    #
    @1
    cA
    cA
    cN
    elfznn0
    nn0cnd
    @2
    cB
    cB
    cN
    elfznn0
    nn0cnd
    cA
    cB
    addcom
    syl2an
end
