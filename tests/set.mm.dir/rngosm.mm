include "crngo.mm"
include "wcel.mm"
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wral.mm"
include "wrex.mm"
include "rngoi.mm"
include "simpld.mm"
include "simprd.mm"

theorem rngosm
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume ringi.1: |- G = ( 1st ` R )
  assume ringi.2: |- H = ( 2nd ` R )
  assume ringi.3: |- X = ran G


  assert |- ( R e. RingOps -> H : ( X X. X ) --> X )

  proof
    cR
    crngo
    wcel
    #
    cG
    cablo
    wcel
    #
    cX
    cX
    cxp
    cX
    cH
    wf
    #
    @0
    @1
    @2
    wa
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    vz
    cv
    #
    cH
    co
    @3
    @4
    @6
    cH
    co
    #
    cH
    co
    wceq
    @3
    @4
    @6
    cG
    co
    cH
    co
    @5
    @3
    @6
    cH
    co
    #
    cG
    co
    wceq
    @3
    @4
    cG
    co
    @6
    cH
    co
    @8
    @7
    cG
    co
    wceq
    w3a
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cX
    wral
    @5
    @4
    wceq
    @4
    @3
    cH
    co
    @4
    wceq
    wa
    vy
    cX
    wral
    vx
    cX
    wrex
    wa
    vx
    vy
    vz
    cR
    cG
    cH
    cX
    ringi.1
    ringi.2
    ringi.3
    rngoi
    simpld
    simprd
end
