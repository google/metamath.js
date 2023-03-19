include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "crg.mm"
include "cgrp.mm"
include "abvrcl.mm"
include "ringgrp.mm"
include "syl.mm"
include "abvf.mm"
include "cv.mm"
include "abveq0.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "abvsubtri.mm"
include "3expb.mm"
include "nrmmetd.mm"

theorem abvmet
  let cA: class A
  let cR: class R
  let cF: class F
  let c.mi: class .-
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume abvmet.x: |- X = ( Base ` R )
  assume abvmet.a: |- A = ( AbsVal ` R )
  assume abvmet.m: |- .- = ( -g ` R )


  assert |- ( F e. A -> ( F o. .- ) e. ( Met ` X ) )

  proof
    cF
    cA
    wcel
    #
    vx
    vy
    cF
    cR
    c.mi
    cX
    cR
    c0g
    cfv
    #
    abvmet.x
    abvmet.m
    @1
    eqid
    #
    @0
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    cA
    cR
    cF
    abvmet.a
    abvrcl
    cR
    ringgrp
    syl
    cA
    cX
    cR
    cF
    abvmet.a
    abvmet.x
    abvf
    cA
    cX
    cR
    cF
    vx
    cv
    #
    @1
    abvmet.a
    abvmet.x
    @2
    abveq0
    @0
    @3
    cX
    wcel
    vy
    cv
    #
    cX
    wcel
    @3
    @4
    c.mi
    co
    cF
    cfv
    @3
    cF
    cfv
    @4
    cF
    cfv
    caddc
    co
    cle
    wbr
    cA
    cX
    cR
    cF
    c.mi
    @3
    @4
    abvmet.a
    abvmet.x
    abvmet.m
    abvsubtri
    3expb
    nrmmetd
end
