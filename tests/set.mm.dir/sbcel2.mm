include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "csb.mm"
include "wb.mm"
include "sbcel12.mm"
include "csbconstg.mm"
include "eleq1d.mm"
include "syl5bb.mm"
include "wn.mm"
include "sbcex.mm"
include "con3i.mm"
include "c0.mm"
include "noel.mm"
include "csbprc.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "2falsed.mm"
include "pm2.61i.mm"

theorem sbcel2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint B x
  assert |- ( [. A / x ]. B e. C <-> B e. [_ A / x ]_ C )

  proof
    cA
    cvv
    wcel
    #
    cB
    cC
    wcel
    #
    vx
    cA
    wsbc
    #
    cB
    vx
    cA
    cC
    csb
    #
    wcel
    #
    wb
    @2
    vx
    cA
    cB
    csb
    #
    @3
    wcel
    @0
    @4
    vx
    cA
    cB
    cC
    sbcel12
    @0
    @5
    cB
    @3
    vx
    cA
    cB
    cvv
    csbconstg
    eleq1d
    syl5bb
    @0
    wn
    #
    @2
    @4
    @2
    @0
    @1
    vx
    cA
    sbcex
    con3i
    @6
    @4
    cB
    c0
    wcel
    cB
    noel
    @6
    @3
    c0
    cB
    vx
    cA
    cC
    csbprc
    eleq2d
    mtbiri
    2falsed
    pm2.61i
end
