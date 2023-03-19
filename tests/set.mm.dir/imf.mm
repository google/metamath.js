include "cc.mm"
include "cr.mm"
include "cv.mm"
include "ci.mm"
include "cdiv.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "df-im.mm"
include "wcel.mm"
include "imval.mm"
include "imcl.mm"
include "eqeltrrd.mm"
include "fmpti.mm"

theorem imf
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- Im : CC --> RR

  proof
    vx
    cc
    cr
    vx
    cv
    #
    ci
    cdiv
    co
    cre
    cfv
    #
    cim
    vx
    df-im
    @0
    cc
    wcel
    @0
    cim
    cfv
    @1
    cr
    @0
    imval
    @0
    imcl
    eqeltrrd
    fmpti
end
