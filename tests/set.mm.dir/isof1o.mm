include "wiso.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "df-isom.mm"
include "simplbi.mm"

theorem isof1o
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( H Isom R , S ( A , B ) -> H : A -1-1-onto-> B )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    cA
    cB
    cH
    wf1o
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    @0
    cH
    cfv
    @1
    cH
    cfv
    cS
    wbr
    wb
    vy
    cA
    wral
    vx
    cA
    wral
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    df-isom
    simplbi
end
