include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cneg.mm"
include "wcel.mm"
include "crab.mm"
include "wex.mm"
include "n0.mm"
include "ssel.mm"
include "wb.mm"
include "renegcl.mm"
include "wceq.mm"
include "negeq.mm"
include "eleq1d.mm"
include "elrab3.mm"
include "syl.mm"
include "recn.mm"
include "negnegd.mm"
include "bitrd.mm"
include "biimprd.mm"
include "syli.mm"
include "elex2.mm"
include "syl6.mm"
include "syl6ibr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"

theorem negn0
  let vz: setvar z
  let cA: class A
  let vx: setvar x
  let vy: setvar y

  disjoint A z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ( A C_ RR /\ A =/= (/) ) -> { z e. RR | -u z e. A } =/= (/) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vz
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vz
    cr
    crab
    #
    c0
    wne
    #
    @1
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    @0
    @6
    vx
    cA
    n0
    @0
    @8
    @6
    vx
    @0
    @8
    vy
    cv
    @5
    wcel
    vy
    wex
    #
    @6
    @0
    @8
    @7
    cneg
    #
    @5
    wcel
    #
    @9
    @8
    @0
    @7
    cr
    wcel
    #
    @11
    cA
    cr
    @7
    ssel
    @12
    @11
    @8
    @12
    @11
    @10
    cneg
    #
    cA
    wcel
    #
    @8
    @12
    @10
    cr
    wcel
    @11
    @14
    wb
    @7
    renegcl
    @4
    @14
    vz
    @10
    cr
    @2
    @10
    wceq
    @3
    @13
    cA
    @2
    @10
    negeq
    eleq1d
    elrab3
    syl
    @12
    @13
    @7
    cA
    @12
    @7
    @7
    recn
    negnegd
    eleq1d
    bitrd
    biimprd
    syli
    vy
    @10
    @5
    elex2
    syl6
    vy
    @5
    n0
    syl6ibr
    exlimdv
    syl5bi
    imp
end
