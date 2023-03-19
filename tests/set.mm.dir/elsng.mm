include "cv.mm"
include "wceq.mm"
include "csn.mm"
include "eqeq1.mm"
include "df-sn.mm"
include "elab2g.mm"

theorem elsng
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. { B } <-> A = B ) )

  proof
    vx
    cv
    #
    cB
    wceq
    cA
    cB
    wceq
    vx
    cA
    cB
    csn
    cV
    @0
    cA
    cB
    eqeq1
    vx
    cB
    df-sn
    elab2g
end
