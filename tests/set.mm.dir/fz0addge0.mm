include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "elfznn0.mm"
include "anim12i.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "addge0.mm"
include "3syl.mm"

theorem fz0addge0
  let cA: class A
  let cB: class B
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ( 0 ... M ) /\ B e. ( 0 ... N ) ) -> 0 <_ ( A + B ) )

  proof
    cA
    cc0
    cM
    cfz
    co
    wcel
    #
    cB
    cc0
    cN
    cfz
    co
    wcel
    #
    wa
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    cc0
    cA
    cB
    caddc
    co
    cle
    wbr
    @0
    @2
    @1
    @3
    cA
    cM
    elfznn0
    cB
    cN
    elfznn0
    anim12i
    @4
    @7
    @10
    @2
    @5
    @3
    @6
    cA
    nn0re
    cB
    nn0re
    anim12i
    @2
    @8
    @3
    @9
    cA
    nn0ge0
    cB
    nn0ge0
    anim12i
    jca
    cA
    cB
    addge0
    3syl
end
