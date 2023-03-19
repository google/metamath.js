include "cv.mm"
include "clininds.mm"
include "wbr.mm"
include "wn.mm"
include "clindeps.mm"
include "wceq.mm"
include "wa.mm"
include "breq12.mm"
include "notbid.mm"
include "df-lindeps.mm"
include "brabga.mm"

theorem lindepsnlininds
  let cS: class S
  let cM: class M
  let cV: class V
  let cW: class W
  let vm: setvar m
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. V /\ M e. W ) -> ( S linDepS M <-> -. S linIndS M ) )

  proof
    vs
    cv
    #
    vm
    cv
    #
    clininds
    wbr
    #
    wn
    cS
    cM
    clininds
    wbr
    #
    wn
    vs
    vm
    cS
    cM
    clindeps
    cV
    cW
    @0
    cS
    wceq
    @1
    cM
    wceq
    wa
    @2
    @3
    @0
    cS
    @1
    cM
    clininds
    breq12
    notbid
    vm
    vs
    df-lindeps
    brabga
end
