include "crngo.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "co.mm"
include "rngosm.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem rngocl
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume ringi.1: |- G = ( 1st ` R )
  assume ringi.2: |- H = ( 2nd ` R )
  assume ringi.3: |- X = ran G


  assert |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( A H B ) e. X )

  proof
    cR
    crngo
    wcel
    cX
    cX
    cxp
    cX
    cH
    wf
    cA
    cX
    wcel
    cB
    cX
    wcel
    cA
    cB
    cH
    co
    cX
    wcel
    cR
    cG
    cH
    cX
    ringi.1
    ringi.2
    ringi.3
    rngosm
    cA
    cB
    cX
    cX
    cX
    cH
    fovrn
    syl3an1
end
