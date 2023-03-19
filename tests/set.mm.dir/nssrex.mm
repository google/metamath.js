include "wss.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "nss.mm"
include "df-rex.mm"
include "bitr4i.mm"

theorem nssrex
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( -. A C_ B <-> E. x e. A -. x e. B )

  proof
    cA
    cB
    wss
    wn
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wn
    #
    wa
    vx
    wex
    @1
    vx
    cA
    wrex
    vx
    cA
    cB
    nss
    @1
    vx
    cA
    df-rex
    bitr4i
end
