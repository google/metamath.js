include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "wral.mm"
include "wi.mm"
include "wex.mm"
include "c0.mm"
include "df-ral.mm"
include "df-ex.mm"
include "ralbii.mm"
include "wa.mm"
include "alnex.mm"
include "imnang.mm"
include "wrex.mm"
include "0el.mm"
include "df-rex.mm"
include "bitri.mm"
include "notbii.mm"
include "3bitr4ri.mm"

theorem n0el
  let vx: setvar x
  let vu: setvar u
  let cA: class A

  disjoint A x
  disjoint u x
  assert |- ( -. (/) e. A <-> A. x e. A E. u u e. x )

  proof
    vu
    cv
    vx
    cv
    #
    wcel
    #
    wn
    vu
    wal
    #
    wn
    #
    vx
    cA
    wral
    @0
    cA
    wcel
    #
    @3
    wi
    vx
    wal
    #
    @1
    vu
    wex
    #
    vx
    cA
    wral
    c0
    cA
    wcel
    #
    wn
    #
    @3
    vx
    cA
    df-ral
    @6
    @3
    vx
    cA
    @1
    vu
    df-ex
    ralbii
    @4
    @2
    wa
    #
    wn
    vx
    wal
    @9
    vx
    wex
    #
    wn
    @5
    @8
    @9
    vx
    alnex
    @4
    @2
    vx
    imnang
    @7
    @10
    @7
    @2
    vx
    cA
    wrex
    @10
    vx
    vu
    cA
    0el
    @2
    vx
    cA
    df-rex
    bitri
    notbii
    3bitr4ri
    3bitr4ri
end
