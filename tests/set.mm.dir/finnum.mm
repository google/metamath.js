include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "ccrd.mm"
include "cdm.mm"
include "isfi.mm"
include "con0.mm"
include "nnon.mm"
include "ensym.mm"
include "isnumi.mm"
include "syl2an.mm"
include "rexlimiva.mm"
include "sylbi.mm"

theorem finnum
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( A e. Fin -> A e. dom card )

  proof
    cA
    cfn
    wcel
    cA
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    cA
    ccrd
    cdm
    wcel
    #
    vx
    cA
    isfi
    @1
    @2
    vx
    com
    @0
    com
    wcel
    @0
    con0
    wcel
    @0
    cA
    cen
    wbr
    @2
    @1
    @0
    nnon
    cA
    @0
    ensym
    @0
    cA
    isnumi
    syl2an
    rexlimiva
    sylbi
end
