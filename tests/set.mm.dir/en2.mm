include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "wex.mm"
include "cpr.mm"
include "c1o.mm"
include "c2o.mm"
include "1onn.mm"
include "df-2o.mm"
include "cen.mm"
include "wbr.mm"
include "en1.mm"
include "biimpi.mm"
include "wcel.mm"
include "df-pr.mm"
include "enp1ilem.mm"
include "eximdv.mm"
include "enp1i.mm"

theorem en2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A ~~ 2o -> E. x E. y A = { x , y } )

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
    csn
    #
    wceq
    #
    vy
    wex
    #
    cA
    @0
    @2
    cpr
    #
    wceq
    #
    vy
    wex
    vx
    cA
    c1o
    c2o
    1onn
    df-2o
    @1
    c1o
    cen
    wbr
    @5
    vy
    @1
    en1
    biimpi
    @0
    cA
    wcel
    @4
    @7
    vy
    vx
    cA
    @3
    @6
    @0
    @2
    df-pr
    enp1ilem
    eximdv
    enp1i
end
