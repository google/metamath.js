include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cpr.mm"
include "wceq.mm"
include "wex.mm"
include "ctp.mm"
include "c2o.mm"
include "c3o.mm"
include "2onn.mm"
include "df-3o.mm"
include "en2.mm"
include "wcel.mm"
include "tpass.mm"
include "enp1ilem.mm"
include "2eximdv.mm"
include "enp1i.mm"

theorem en3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A ~~ 3o -> E. x E. y E. z A = { x , y , z } )

  proof
    cA
    vx
    cv
    #
    csn
    cdif
    #
    vy
    cv
    #
    vz
    cv
    #
    cpr
    #
    wceq
    #
    vz
    wex
    vy
    wex
    cA
    @0
    @2
    @3
    ctp
    #
    wceq
    #
    vz
    wex
    vy
    wex
    vx
    cA
    c2o
    c3o
    2onn
    df-3o
    vy
    vz
    @1
    en2
    @0
    cA
    wcel
    @5
    @7
    vy
    vz
    vx
    cA
    @4
    @6
    @0
    @2
    @3
    tpass
    enp1ilem
    2eximdv
    enp1i
end
