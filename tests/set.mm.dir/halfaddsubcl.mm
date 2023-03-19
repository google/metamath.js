include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "addcl.mm"
include "halfcl.mm"
include "syl.mm"
include "subcl.mm"
include "jca.mm"

theorem halfaddsubcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( ( A + B ) / 2 ) e. CC /\ ( ( A - B ) / 2 ) e. CC ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    cc
    wcel
    #
    cA
    cB
    cmin
    co
    #
    c2
    cdiv
    co
    cc
    wcel
    #
    @0
    @1
    cc
    wcel
    @2
    cA
    cB
    addcl
    @1
    halfcl
    syl
    @0
    @3
    cc
    wcel
    @4
    cA
    cB
    subcl
    @3
    halfcl
    syl
    jca
end
