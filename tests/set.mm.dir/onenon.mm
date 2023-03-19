include "con0.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "ccrd.mm"
include "cdm.mm"
include "enrefg.mm"
include "isnumi.mm"
include "mpdan.mm"

theorem onenon
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( A e. On -> A e. dom card )

  proof
    cA
    con0
    wcel
    cA
    cA
    cen
    wbr
    cA
    ccrd
    cdm
    wcel
    cA
    con0
    enrefg
    cA
    cA
    isnumi
    mpdan
end
