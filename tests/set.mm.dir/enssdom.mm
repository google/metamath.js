include "cen.mm"
include "cdom.mm"
include "relen.mm"
include "cv.mm"
include "cop.mm"
include "wf1o.mm"
include "wex.mm"
include "copab.mm"
include "wcel.mm"
include "wf1.mm"
include "f1of1.mm"
include "eximi.mm"
include "opabid.mm"
include "3imtr4i.mm"
include "df-en.mm"
include "eleq2i.mm"
include "df-dom.mm"
include "relssi.mm"

theorem enssdom
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cA: class A


  assert |- ~~ C_ ~<_

  proof
    vx
    vy
    cen
    cdom
    relen
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    @1
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    vx
    vy
    copab
    #
    wcel
    #
    @2
    @0
    @1
    @3
    wf1
    #
    vf
    wex
    #
    vx
    vy
    copab
    #
    wcel
    #
    @2
    cen
    wcel
    @2
    cdom
    wcel
    @5
    @9
    @7
    @11
    @4
    @8
    vf
    @0
    @1
    @3
    f1of1
    eximi
    @5
    vx
    vy
    opabid
    @9
    vx
    vy
    opabid
    3imtr4i
    cen
    @6
    @2
    vx
    vy
    vf
    df-en
    eleq2i
    cdom
    @10
    @2
    vx
    vy
    vf
    df-dom
    eleq2i
    3imtr4i
    relssi
end
