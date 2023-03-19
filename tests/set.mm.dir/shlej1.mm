include "csh.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "simpr.mm"
include "unss1.mm"
include "chil.mm"
include "wi.mm"
include "simpl1.mm"
include "shss.mm"
include "syl.mm"
include "simpl3.mm"
include "unssd.mm"
include "simpl2.mm"
include "occon2.mm"
include "syl2anc.mm"
include "syl5.mm"
include "mpd.mm"
include "wceq.mm"
include "shjval.mm"
include "3sstr4d.mm"

theorem shlej1
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( ( A e. SH /\ B e. SH /\ C e. SH ) /\ A C_ B ) -> ( A vH C ) C_ ( B vH C ) )

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
    #
    cA
    cC
    cun
    #
    cort
    cfv
    cort
    cfv
    #
    cB
    cC
    cun
    #
    cort
    cfv
    cort
    cfv
    #
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
    @5
    @4
    @7
    @9
    wss
    #
    @3
    @4
    simpr
    @4
    @6
    @8
    wss
    #
    @5
    @12
    cA
    cB
    cC
    unss1
    @5
    @6
    chil
    wss
    @8
    chil
    wss
    @13
    @12
    wi
    @5
    cA
    cC
    chil
    @5
    @0
    cA
    chil
    wss
    @0
    @1
    @2
    @4
    simpl1
    #
    cA
    shss
    syl
    @5
    @2
    cC
    chil
    wss
    @0
    @1
    @2
    @4
    simpl3
    #
    cC
    shss
    syl
    #
    unssd
    @5
    cB
    cC
    chil
    @5
    @1
    cB
    chil
    wss
    @0
    @1
    @2
    @4
    simpl2
    #
    cB
    shss
    syl
    @16
    unssd
    @6
    @8
    occon2
    syl2anc
    syl5
    mpd
    @5
    @0
    @2
    @10
    @7
    wceq
    @14
    @15
    cA
    cC
    shjval
    syl2anc
    @5
    @1
    @2
    @11
    @9
    wceq
    @17
    @15
    cB
    cC
    shjval
    syl2anc
    3sstr4d
end
