include "wsbc.mm"
include "csb.mm"
include "sbccom2f.mm"
include "wceq.mm"
include "wb.mm"
include "dfsbcq.mm"
include "ax-mp.mm"
include "sbcbii.mm"
include "3bitri.mm"

theorem sbccom2fi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume sbccom2fi.1: |- A e. _V
  assume sbccom2fi.2: |- F/_ y A
  assume sbccom2fi.3: |- [_ A / x ]_ B = C
  assume sbccom2fi.4: |- ( [. A / x ]. ph <-> ps )

  disjoint x y
  assert |- ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ps )

  proof
    wph
    vy
    cB
    wsbc
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    vy
    vx
    cA
    cB
    csb
    #
    wsbc
    #
    @0
    vy
    cC
    wsbc
    #
    wps
    vy
    cC
    wsbc
    wph
    vx
    vy
    cA
    cB
    sbccom2fi.1
    sbccom2fi.2
    sbccom2f
    @1
    cC
    wceq
    @2
    @3
    wb
    sbccom2fi.3
    @0
    vy
    @1
    cC
    dfsbcq
    ax-mp
    @0
    wps
    vy
    cC
    sbccom2fi.4
    sbcbii
    3bitri
end
