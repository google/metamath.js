include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "df-cnv.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfopab.mm"
include "nfcxfr.mm"

theorem nfcnv
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  assume nfcnv.1: |- F/_ x A


  assert |- F/_ x `' A

  proof
    vx
    cA
    ccnv
    vz
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vy
    vz
    copab
    vy
    vz
    cA
    df-cnv
    @2
    vy
    vz
    vx
    vx
    @0
    @1
    cA
    vx
    @0
    nfcv
    nfcnv.1
    vx
    @1
    nfcv
    nfbr
    nfopab
    nfcxfr
end
