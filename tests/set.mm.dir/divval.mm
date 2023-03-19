include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "crio.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "eqeq2.mm"
include "riotabidv.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "df-div.mm"
include "riotaex.mm"
include "ovmpt2.mm"
include "sylan2br.mm"
include "3impb.mm"

theorem divval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( A / B ) = ( iota_ x e. CC ( B x. x ) = A ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cA
    cB
    cdiv
    co
    cB
    vx
    cv
    #
    cmul
    co
    #
    cA
    wceq
    #
    vx
    cc
    crio
    #
    wceq
    #
    @1
    @2
    wa
    @0
    cB
    cc
    cc0
    csn
    cdif
    #
    wcel
    @7
    cB
    cc
    cc0
    eldifsn
    vz
    vy
    cA
    cB
    cc
    @8
    vy
    cv
    #
    @3
    cmul
    co
    #
    vz
    cv
    #
    wceq
    #
    vx
    cc
    crio
    @6
    cdiv
    @10
    cA
    wceq
    #
    vx
    cc
    crio
    @11
    cA
    wceq
    @12
    @13
    vx
    cc
    @11
    cA
    @10
    eqeq2
    riotabidv
    @9
    cB
    wceq
    #
    @13
    @5
    vx
    cc
    @14
    @10
    @4
    cA
    @9
    cB
    @3
    cmul
    oveq1
    eqeq1d
    riotabidv
    vz
    vy
    vx
    df-div
    @5
    vx
    cc
    riotaex
    ovmpt2
    sylan2br
    3impb
end
