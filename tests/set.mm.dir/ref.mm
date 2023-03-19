include "cc.mm"
include "cr.mm"
include "cv.mm"
include "ccj.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cre.mm"
include "df-re.mm"
include "wcel.mm"
include "reval.mm"
include "recl.mm"
include "eqeltrrd.mm"
include "fmpti.mm"

theorem ref
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- Re : CC --> RR

  proof
    vx
    cc
    cr
    vx
    cv
    #
    @0
    ccj
    cfv
    caddc
    co
    c2
    cdiv
    co
    #
    cre
    vx
    df-re
    @0
    cc
    wcel
    @0
    cre
    cfv
    @1
    cr
    @0
    reval
    @0
    recl
    eqeltrrd
    fmpti
end
