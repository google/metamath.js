include "wral.mm"
include "wsbc.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "sbcbii.mm"
include "cvv.mm"
include "wb.mm"
include "sbcimg.mm"
include "ax-mp.mm"
include "bnj525.mm"
include "imbi1i.mm"
include "bitri.mm"
include "albii.mm"
include "sbcal.mm"
include "3bitr4i.mm"

theorem bnj538OLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume bnj538OLD.1: |- A e. _V

  disjoint A x
  disjoint B y
  disjoint x y
  assert |- ( [. A / y ]. A. x e. B ph <-> A. x e. B [. A / y ]. ph )

  proof
    wph
    vx
    cB
    wral
    #
    vy
    cA
    wsbc
    vx
    cv
    cB
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    vy
    cA
    wsbc
    #
    wph
    vy
    cA
    wsbc
    #
    vx
    cB
    wral
    #
    @0
    @3
    vy
    cA
    wph
    vx
    cB
    df-ral
    sbcbii
    @2
    vy
    cA
    wsbc
    #
    vx
    wal
    @1
    @5
    wi
    #
    vx
    wal
    @4
    @6
    @7
    @8
    vx
    @7
    @1
    vy
    cA
    wsbc
    #
    @5
    wi
    #
    @8
    cA
    cvv
    wcel
    @7
    @10
    wb
    bnj538OLD.1
    @1
    wph
    vy
    cA
    cvv
    sbcimg
    ax-mp
    @9
    @1
    @5
    @1
    vy
    cA
    bnj538OLD.1
    bnj525
    imbi1i
    bitri
    albii
    @2
    vx
    vy
    cA
    sbcal
    @5
    vx
    cB
    df-ral
    3bitr4i
    bitri
end
