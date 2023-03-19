include "csh.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "shlej1.mm"
include "wceq.mm"
include "shjcom.mm"
include "3adant2.mm"
include "adantr.mm"
include "3adant1.mm"
include "3sstr3d.mm"

theorem shlej2
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( ( A e. SH /\ B e. SH /\ C e. SH ) /\ A C_ B ) -> ( C vH A ) C_ ( C vH B ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    cC
    csh
    wcel
    #
    w3a
    #
    cA
    cB
    wss
    #
    wa
    cA
    cC
    chj
    co
    #
    cB
    cC
    chj
    co
    #
    cC
    cA
    chj
    co
    #
    cC
    cB
    chj
    co
    #
    cA
    cB
    cC
    shlej1
    @3
    @5
    @7
    wceq
    #
    @4
    @0
    @2
    @9
    @1
    cA
    cC
    shjcom
    3adant2
    adantr
    @3
    @6
    @8
    wceq
    #
    @4
    @1
    @2
    @10
    @0
    cB
    cC
    shjcom
    3adant1
    adantr
    3sstr3d
end
