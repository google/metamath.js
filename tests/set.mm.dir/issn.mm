include "weq.mm"
include "wral.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "wcel.mm"
include "wb.mm"
include "equcom.mm"
include "a1i.mm"
include "ralbidv.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "eqsn.mm"
include "syl.mm"
include "bitr4d.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "spcegv.mm"
include "sylbid.mm"
include "rexlimiv.mm"

theorem issn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( E. x e. A A. y e. A x = y -> E. z A = { z } )

  proof
    vx
    vy
    weq
    #
    vy
    cA
    wral
    #
    cA
    vz
    cv
    #
    csn
    #
    wceq
    #
    vz
    wex
    #
    vx
    cA
    vx
    cv
    #
    cA
    wcel
    #
    @1
    cA
    @6
    csn
    #
    wceq
    #
    @5
    @7
    @1
    vy
    vx
    weq
    #
    vy
    cA
    wral
    #
    @9
    @7
    @0
    @10
    vy
    cA
    @0
    @10
    wb
    @7
    vx
    vy
    equcom
    a1i
    ralbidv
    @7
    cA
    c0
    wne
    @9
    @11
    wb
    cA
    @6
    ne0i
    vy
    cA
    @6
    eqsn
    syl
    bitr4d
    @4
    @9
    vz
    @6
    cA
    vz
    vx
    weq
    @3
    @8
    cA
    @2
    @6
    sneq
    eqeq2d
    spcegv
    sylbid
    rexlimiv
end
