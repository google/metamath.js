include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "wdisj.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "wmo.mm"
include "wal.mm"
include "df-ral.mm"
include "wn.mm"
include "simprr.mm"
include "n0i.mm"
include "syl.mm"
include "simpl.mm"
include "adantl.mm"
include "eldif.mm"
include "syl5bir.mm"
include "mpand.mm"
include "mt3d.mm"
include "jca.mm"
include "ex.mm"
include "alimi.mm"
include "sylbi.mm"
include "moim.mm"
include "alimdv.mm"
include "dfdisj2.mm"
include "3imtr4g.mm"
include "disjss1.mm"
include "adantr.mm"
include "impbid.mm"

theorem disjss3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( ( A C_ B /\ A. x e. ( B \ A ) C = (/) ) -> ( Disj_ x e. A C <-> Disj_ x e. B C ) )

  proof
    cA
    cB
    wss
    #
    cC
    c0
    wceq
    #
    vx
    cB
    cA
    cdif
    #
    wral
    #
    wa
    vx
    cA
    cC
    wdisj
    #
    vx
    cB
    cC
    wdisj
    #
    @3
    @4
    @5
    wi
    @0
    @3
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cC
    wcel
    #
    wa
    #
    vx
    wmo
    #
    vy
    wal
    @6
    cB
    wcel
    #
    @9
    wa
    #
    vx
    wmo
    #
    vy
    wal
    @4
    @5
    @3
    @11
    @14
    vy
    @3
    @13
    @10
    wi
    #
    vx
    wal
    #
    @11
    @14
    wi
    @3
    @6
    @2
    wcel
    #
    @1
    wi
    #
    vx
    wal
    @16
    @1
    vx
    @2
    df-ral
    @18
    @15
    vx
    @18
    @13
    @10
    @18
    @13
    wa
    #
    @7
    @9
    @19
    @7
    @1
    @19
    @9
    @1
    wn
    @18
    @12
    @9
    simprr
    #
    cC
    @8
    n0i
    syl
    @19
    @12
    @7
    wn
    #
    @1
    @13
    @12
    @18
    @12
    @9
    simpl
    adantl
    @12
    @21
    wa
    @17
    @19
    @1
    @6
    cB
    cA
    eldif
    @18
    @13
    simpl
    syl5bir
    mpand
    mt3d
    @20
    jca
    ex
    alimi
    sylbi
    @13
    @10
    vx
    moim
    syl
    alimdv
    vx
    vy
    cA
    cC
    dfdisj2
    vx
    vy
    cB
    cC
    dfdisj2
    3imtr4g
    adantl
    @0
    @5
    @4
    wi
    @3
    vx
    cA
    cB
    cC
    disjss1
    adantr
    impbid
end
