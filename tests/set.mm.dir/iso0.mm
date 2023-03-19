include "c0.mm"
include "wiso.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "f1o0.mm"
include "ral0.mm"
include "df-isom.mm"
include "mpbir2an.mm"

theorem iso0
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y


  assert |- (/) Isom R , S ( (/) , (/) )

  proof
    c0
    c0
    cR
    cS
    c0
    wiso
    c0
    c0
    c0
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
    c0
    cfv
    @1
    c0
    cfv
    cS
    wbr
    wb
    vy
    c0
    wral
    #
    vx
    c0
    wral
    f1o0
    @2
    vx
    ral0
    vx
    vy
    c0
    c0
    cR
    cS
    c0
    df-isom
    mpbir2an
end
