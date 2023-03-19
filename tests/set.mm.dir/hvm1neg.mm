include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "csm.mm"
include "wceq.mm"
include "neg1cn.mm"
include "ax-hvmulass.mm"
include "mp3an1.mm"
include "mulm1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem hvm1neg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. ~H ) -> ( -u 1 .h ( A .h B ) ) = ( -u A .h B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    c1
    cneg
    #
    cA
    cmul
    co
    #
    cB
    csm
    co
    #
    @3
    cA
    cB
    csm
    co
    csm
    co
    #
    cA
    cneg
    #
    cB
    csm
    co
    @3
    cc
    wcel
    @0
    @1
    @5
    @6
    wceq
    neg1cn
    @3
    cA
    cB
    ax-hvmulass
    mp3an1
    @2
    @4
    @7
    cB
    csm
    @0
    @4
    @7
    wceq
    @1
    cA
    mulm1
    adantr
    oveq1d
    eqtr3d
end
