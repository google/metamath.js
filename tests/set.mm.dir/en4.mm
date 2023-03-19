include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "ctp.mm"
include "wceq.mm"
include "wex.mm"
include "cpr.mm"
include "cun.mm"
include "c3o.mm"
include "c4o.mm"
include "3onn.mm"
include "df-4o.mm"
include "en3.mm"
include "wcel.mm"
include "qdassr.mm"
include "enp1ilem.mm"
include "eximdv.mm"
include "2eximdv.mm"
include "enp1i.mm"

theorem en4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A ~~ 4o -> E. x E. y E. z E. w A = ( { x , y } u. { z , w } ) )

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
    vw
    cv
    #
    ctp
    #
    wceq
    #
    vw
    wex
    #
    vz
    wex
    vy
    wex
    cA
    @0
    @2
    cpr
    @3
    @4
    cpr
    cun
    #
    wceq
    #
    vw
    wex
    #
    vz
    wex
    vy
    wex
    vx
    cA
    c3o
    c4o
    3onn
    df-4o
    vy
    vz
    vw
    @1
    en3
    @0
    cA
    wcel
    #
    @7
    @10
    vy
    vz
    @11
    @6
    @9
    vw
    vx
    cA
    @5
    @8
    @0
    @2
    @3
    @4
    qdassr
    enp1ilem
    eximdv
    2eximdv
    enp1i
end
