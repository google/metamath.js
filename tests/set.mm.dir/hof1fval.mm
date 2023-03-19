include "chomf.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "chom.mm"
include "co.mm"
include "c2nd.mm"
include "cco.mm"
include "cop.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "eqid.mm"
include "hofval.mm"
include "fvex.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "op1std.mm"
include "syl.mm"

theorem hof1fval
  let wph: wff ph
  let cC: class C
  let cM: class M
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume hofval.m: |- M = ( HomF ` C )
  assume hofval.c: |- ( ph -> C e. Cat )


  assert |- ( ph -> ( 1st ` M ) = ( Homf ` C ) )

  proof
    wph
    cM
    cC
    chomf
    cfv
    #
    vx
    vy
    cC
    cbs
    cfv
    #
    @1
    cxp
    #
    @2
    vf
    vg
    vy
    cv
    #
    c1st
    cfv
    #
    vx
    cv
    #
    c1st
    cfv
    #
    cC
    chom
    cfv
    #
    co
    @5
    c2nd
    cfv
    @3
    c2nd
    cfv
    #
    @7
    co
    vh
    @5
    @7
    cfv
    vg
    cv
    vh
    cv
    @5
    @8
    cC
    cco
    cfv
    #
    co
    co
    vf
    cv
    @4
    @6
    cop
    @8
    @9
    co
    co
    cmpt
    cmpt2
    #
    cmpt2
    #
    cop
    wceq
    cM
    c1st
    cfv
    @0
    wceq
    wph
    vx
    vy
    @1
    cC
    @9
    vf
    vg
    vh
    @7
    cM
    hofval.m
    hofval.c
    @1
    eqid
    @7
    eqid
    @9
    eqid
    hofval
    @0
    @11
    cM
    cC
    chomf
    fvex
    vx
    vy
    @2
    @2
    @10
    @1
    @1
    cC
    cbs
    fvex
    #
    @12
    xpex
    #
    @13
    mpt2ex
    op1std
    syl
end
