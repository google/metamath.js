include "cvc.mm"
include "wcel.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "co.mm"
include "vcsm.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem vccl
  let cA: class A
  let cB: class B
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume vciOLD.1: |- G = ( 1st ` W )
  assume vciOLD.2: |- S = ( 2nd ` W )
  assume vciOLD.3: |- X = ran G


  assert |- ( ( W e. CVecOLD /\ A e. CC /\ B e. X ) -> ( A S B ) e. X )

  proof
    cW
    cvc
    wcel
    cc
    cX
    cxp
    cX
    cS
    wf
    cA
    cc
    wcel
    cB
    cX
    wcel
    cA
    cB
    cS
    co
    cX
    wcel
    cS
    cG
    cW
    cX
    vciOLD.1
    vciOLD.2
    vciOLD.3
    vcsm
    cA
    cB
    cX
    cc
    cX
    cS
    fovrn
    syl3an1
end
