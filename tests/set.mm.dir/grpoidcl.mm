include "cgr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crio.mm"
include "grpoidval.mm"
include "wreu.mm"
include "grpoideu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem grpoidcl
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vu: setvar u
  assume grpoidval.1: |- X = ran G
  assume grpoidval.2: |- U = ( GId ` G )


  assert |- ( G e. GrpOp -> U e. X )

  proof
    cG
    cgr
    wcel
    #
    cU
    vu
    cv
    vx
    cv
    #
    cG
    co
    @1
    wceq
    vx
    cX
    wral
    #
    vu
    cX
    crio
    #
    cX
    vx
    vu
    cU
    cG
    cX
    grpoidval.1
    grpoidval.2
    grpoidval
    @0
    @2
    vu
    cX
    wreu
    @3
    cX
    wcel
    vx
    vu
    cG
    cX
    grpoidval.1
    grpoideu
    @2
    vu
    cX
    riotacl
    syl
    eqeltrd
end
