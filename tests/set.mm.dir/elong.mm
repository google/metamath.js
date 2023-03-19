include "cv.mm"
include "word.mm"
include "con0.mm"
include "ordeq.mm"
include "df-on.mm"
include "elab2g.mm"

theorem elong
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. On <-> Ord A ) )

  proof
    vx
    cv
    #
    word
    cA
    word
    vx
    cA
    con0
    cV
    @0
    cA
    ordeq
    vx
    df-on
    elab2g
end
