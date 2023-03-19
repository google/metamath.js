include "cvc.mm"
include "wcel.mm"
include "cablo.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "c1.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "wa.mm"
include "vciOLD.mm"
include "simp2d.mm"

theorem vcsm
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume vciOLD.1: |- G = ( 1st ` W )
  assume vciOLD.2: |- S = ( 2nd ` W )
  assume vciOLD.3: |- X = ran G


  assert |- ( W e. CVecOLD -> S : ( CC X. X ) --> X )

  proof
    cW
    cvc
    wcel
    cG
    cablo
    wcel
    cc
    cX
    cxp
    cX
    cS
    wf
    c1
    vx
    cv
    #
    cS
    co
    @0
    wceq
    vy
    cv
    #
    @0
    vz
    cv
    #
    cG
    co
    cS
    co
    @1
    @0
    cS
    co
    #
    @1
    @2
    cS
    co
    cG
    co
    wceq
    vz
    cX
    wral
    @1
    @2
    caddc
    co
    @0
    cS
    co
    @3
    @2
    @0
    cS
    co
    #
    cG
    co
    wceq
    @1
    @2
    cmul
    co
    @0
    cS
    co
    @1
    @4
    cS
    co
    wceq
    wa
    vz
    cc
    wral
    wa
    vy
    cc
    wral
    wa
    vx
    cX
    wral
    vx
    vy
    vz
    cS
    cG
    cW
    cX
    vciOLD.1
    vciOLD.2
    vciOLD.3
    vciOLD
    simp2d
end
