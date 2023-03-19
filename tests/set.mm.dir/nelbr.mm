include "wel.mm"
include "wn.mm"
include "wcel.mm"
include "cnelbr.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "eleq12.mm"
include "notbid.mm"
include "df-nelbr.mm"
include "brabga.mm"

theorem nelbr
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( ( A e. V /\ B e. W ) -> ( A e// B <-> -. A e. B ) )

  proof
    vx
    vy
    wel
    #
    wn
    cA
    cB
    wcel
    #
    wn
    vx
    vy
    cA
    cB
    cnelbr
    cV
    cW
    vx
    cv
    #
    cA
    wceq
    vy
    cv
    #
    cB
    wceq
    wa
    @0
    @1
    @2
    cA
    @3
    cB
    eleq12
    notbid
    vx
    vy
    df-nelbr
    brabga
end
