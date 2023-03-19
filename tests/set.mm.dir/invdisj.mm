include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wal.mm"
include "wdisj.mm"
include "nfra2.mm"
include "wi.mm"
include "df-ral.mm"
include "rsp.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "imim2i.mm"
include "impd.mm"
include "alimi.mm"
include "sylbi.mm"
include "mo2icl.mm"
include "syl.mm"
include "alrimi.mm"
include "dfdisj2.mm"
include "sylibr.mm"

theorem invdisj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C x
  assert |- ( A. x e. A A. y e. B C = x -> Disj_ x e. A B )

  proof
    cC
    vx
    cv
    #
    wceq
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @0
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wa
    #
    vx
    wmo
    #
    vy
    wal
    vx
    cA
    cB
    wdisj
    @3
    @7
    vy
    @1
    vx
    vy
    cA
    cB
    nfra2
    @3
    @6
    @0
    cC
    wceq
    #
    wi
    #
    vx
    wal
    #
    @7
    @3
    @4
    @2
    wi
    #
    vx
    wal
    @10
    @2
    vx
    cA
    df-ral
    @11
    @9
    vx
    @11
    @4
    @5
    @8
    @2
    @5
    @8
    wi
    @4
    @2
    @5
    @1
    @8
    @1
    vy
    cB
    rsp
    cC
    @0
    eqcom
    syl6ib
    imim2i
    impd
    alimi
    sylbi
    @6
    vx
    cC
    mo2icl
    syl
    alrimi
    vx
    vy
    cA
    cB
    dfdisj2
    sylibr
end
