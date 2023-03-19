include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "wb.mm"
include "df-in.mm"
include "eqeq1i.mm"
include "abeq1.mm"
include "imnan.mm"
include "noel.mm"
include "nbn.mm"
include "bitr2i.mm"
include "albii.mm"
include "3bitri.mm"
include "df-ral.mm"
include "bitr4i.mm"

theorem disj
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( ( A i^i B ) = (/) <-> A. x e. A -. x e. B )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    #
    vx
    cv
    #
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wn
    #
    wi
    #
    vx
    wal
    #
    @5
    vx
    cA
    wral
    @1
    @3
    @4
    wa
    #
    vx
    cab
    #
    c0
    wceq
    @8
    @2
    c0
    wcel
    #
    wb
    #
    vx
    wal
    @7
    @0
    @9
    c0
    vx
    cA
    cB
    df-in
    eqeq1i
    @8
    vx
    c0
    abeq1
    @11
    @6
    vx
    @6
    @8
    wn
    @11
    @3
    @4
    imnan
    @10
    @8
    @2
    noel
    nbn
    bitr2i
    albii
    3bitri
    @5
    vx
    cA
    df-ral
    bitr4i
end
