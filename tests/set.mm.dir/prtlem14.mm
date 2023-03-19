include "wprt.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "df-prt.mm"
include "rsp2.mm"
include "sylbi.mm"
include "elin.mm"
include "wn.mm"
include "wal.mm"
include "eq0.mm"
include "sp.mm"
include "pm2.21d.mm"
include "syl5bir.mm"
include "jao1i.mm"
include "syl6.mm"

theorem prtlem14
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z

  disjoint w x
  disjoint w y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( Prt A -> ( ( x e. A /\ y e. A ) -> ( ( w e. x /\ w e. y ) -> x = y ) ) )

  proof
    cA
    wprt
    #
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cA
    wcel
    wa
    #
    @1
    @2
    wceq
    #
    @1
    @2
    cin
    #
    c0
    wceq
    #
    wo
    #
    vw
    cv
    #
    @1
    wcel
    @8
    @2
    wcel
    wa
    #
    @4
    wi
    @0
    @7
    vy
    cA
    wral
    vx
    cA
    wral
    @3
    @7
    wi
    vx
    vy
    cA
    df-prt
    @7
    vx
    vy
    cA
    cA
    rsp2
    sylbi
    @4
    @6
    @9
    @9
    @8
    @5
    wcel
    #
    @6
    @4
    @8
    @1
    @2
    elin
    @6
    @10
    @4
    @6
    @10
    wn
    #
    vw
    wal
    @11
    vw
    @5
    eq0
    @11
    vw
    sp
    sylbi
    pm2.21d
    syl5bir
    jao1i
    syl6
end
