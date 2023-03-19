include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "cv.mm"
include "wss.mm"
include "cufil.mm"
include "wrex.mm"
include "cvv.mm"
include "filtop.mm"
include "pwexg.mm"
include "numth3.mm"
include "4syl.mm"
include "filssufilg.mm"
include "mpdan.mm"

theorem filssufil
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x

  disjoint F f
  disjoint X f
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint g h
  disjoint g x
  disjoint F g
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint X g
  disjoint X h
  disjoint X x
  assert |- ( F e. ( Fil ` X ) -> E. f e. ( UFil ` X ) F C_ f )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cX
    cpw
    #
    cpw
    #
    ccrd
    cdm
    wcel
    #
    cF
    vf
    cv
    wss
    vf
    cX
    cufil
    cfv
    wrex
    @0
    cX
    cF
    wcel
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @3
    cF
    cX
    filtop
    cX
    cF
    pwexg
    @1
    cvv
    pwexg
    @2
    cvv
    numth3
    4syl
    vf
    cF
    cX
    filssufilg
    mpdan
end
