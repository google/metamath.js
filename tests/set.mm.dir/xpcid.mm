include "cop.mm"
include "cfv.mm"
include "co.mm"
include "df-ov.mm"
include "cv.mm"
include "cvv.mm"
include "ccid.mm"
include "cmpt2.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "xpccatid.mm"
include "simprd.mm"
include "syl5eq.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2d.mm"
include "simprr.mm"
include "opeq12d.mm"
include "opex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "syl5eqr.mm"

theorem xpcid
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let c.1: class .1.
  let cI: class I
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume xpccat.t: |- T = ( C Xc. D )
  assume xpccat.c: |- ( ph -> C e. Cat )
  assume xpccat.d: |- ( ph -> D e. Cat )
  assume xpccat.x: |- X = ( Base ` C )
  assume xpccat.y: |- Y = ( Base ` D )
  assume xpccat.i: |- I = ( Id ` C )
  assume xpccat.j: |- J = ( Id ` D )
  assume xpcid.1: |- .1. = ( Id ` T )
  assume xpcid.r: |- ( ph -> R e. X )
  assume xpcid.s: |- ( ph -> S e. Y )


  assert |- ( ph -> ( .1. ` <. R , S >. ) = <. ( I ` R ) , ( J ` S ) >. )

  proof
    wph
    cR
    cS
    cop
    c.1
    cfv
    cR
    cS
    c.1
    co
    cR
    cI
    cfv
    #
    cS
    cJ
    cfv
    #
    cop
    #
    cR
    cS
    c.1
    df-ov
    wph
    vx
    vy
    cR
    cS
    cX
    cY
    vx
    cv
    #
    cI
    cfv
    #
    vy
    cv
    #
    cJ
    cfv
    #
    cop
    #
    @2
    c.1
    cvv
    wph
    c.1
    cT
    ccid
    cfv
    #
    vx
    vy
    cX
    cY
    @7
    cmpt2
    #
    xpcid.1
    wph
    cT
    ccat
    wcel
    @8
    @9
    wceq
    wph
    vx
    vy
    cC
    cD
    cT
    cI
    cJ
    cX
    cY
    xpccat.t
    xpccat.c
    xpccat.d
    xpccat.x
    xpccat.y
    xpccat.i
    xpccat.j
    xpccatid
    simprd
    syl5eq
    wph
    @3
    cR
    wceq
    #
    @5
    cS
    wceq
    #
    wa
    wa
    #
    @4
    @0
    @6
    @1
    @12
    @3
    cR
    cI
    wph
    @10
    @11
    simprl
    fveq2d
    @12
    @5
    cS
    cJ
    wph
    @10
    @11
    simprr
    fveq2d
    opeq12d
    xpcid.r
    xpcid.s
    @2
    cvv
    wcel
    wph
    @0
    @1
    opex
    a1i
    ovmpt2d
    syl5eqr
end
