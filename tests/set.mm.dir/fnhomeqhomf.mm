include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "fnov.mm"
include "homffval.mm"
include "eqeq2.mm"
include "mpbiri.mm"
include "sylbi.mm"

theorem fnhomeqhomf
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph
  let cX: class X
  let cY: class Y
  assume homffval.f: |- F = ( Homf ` C )
  assume homffval.b: |- B = ( Base ` C )
  assume homffval.h: |- H = ( Hom ` C )


  assert |- ( H Fn ( B X. B ) -> F = H )

  proof
    cH
    cB
    cB
    cxp
    wfn
    cH
    vx
    vy
    cB
    cB
    vx
    cv
    vy
    cv
    cH
    co
    cmpt2
    #
    wceq
    #
    cF
    cH
    wceq
    #
    vx
    vy
    cB
    cB
    cH
    fnov
    @1
    @2
    cF
    @0
    wceq
    vx
    vy
    cB
    cC
    cF
    cH
    homffval.f
    homffval.b
    homffval.h
    homffval
    cH
    @0
    cF
    eqeq2
    mpbiri
    sylbi
end
