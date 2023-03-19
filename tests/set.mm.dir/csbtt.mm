include "wcel.mm"
include "wnfc.mm"
include "wa.mm"
include "csb.mm"
include "cv.mm"
include "wsbc.mm"
include "cab.mm"
include "df-csb.mm"
include "wnf.mm"
include "wb.mm"
include "nfcr.mm"
include "sbctt.mm"
include "sylan2.mm"
include "abbi1dv.mm"
include "syl5eq.mm"

theorem csbtt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y


  assert |- ( ( A e. V /\ F/_ x B ) -> [_ A / x ]_ B = B )

  proof
    cA
    cV
    wcel
    #
    vx
    cB
    wnfc
    #
    wa
    #
    vx
    cA
    cB
    csb
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    cB
    vx
    vy
    cA
    cB
    df-csb
    @2
    @4
    vy
    cB
    @1
    @0
    @3
    vx
    wnf
    @4
    @3
    wb
    vx
    vy
    cB
    nfcr
    @3
    vx
    cA
    cV
    sbctt
    sylan2
    abbi1dv
    syl5eq
end
