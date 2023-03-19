include "ccom.mm"
include "cvv.mm"
include "cxp.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "ccnv.mm"
include "cuni.mm"
include "cmpt.mm"
include "ctpos.mm"
include "coass.mm"
include "dftpos4.mm"
include "coeq2i.mm"
include "3eqtr4i.mm"

theorem tposco
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z


  assert |- tpos ( F o. G ) = ( F o. tpos G )

  proof
    cF
    cG
    ccom
    #
    vx
    cvv
    cvv
    cxp
    c0
    csn
    cun
    vx
    cv
    csn
    ccnv
    cuni
    cmpt
    #
    ccom
    cF
    cG
    @1
    ccom
    #
    ccom
    @0
    ctpos
    cF
    cG
    ctpos
    #
    ccom
    cF
    cG
    @1
    coass
    vx
    @0
    dftpos4
    @3
    @2
    cF
    vx
    cG
    dftpos4
    coeq2i
    3eqtr4i
end
