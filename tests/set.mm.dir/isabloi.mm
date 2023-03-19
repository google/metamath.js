include "cablo.mm"
include "wcel.mm"
include "cgr.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "rgen2a.mm"
include "grporn.mm"
include "isablo.mm"
include "mpbir2an.mm"

theorem isabloi
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cX: class X
  assume isabli.1: |- G e. GrpOp
  assume isabli.2: |- dom G = ( X X. X )
  assume isabli.3: |- ( ( x e. X /\ y e. X ) -> ( x G y ) = ( y G x ) )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  assert |- G e. AbelOp

  proof
    cG
    cablo
    wcel
    cG
    cgr
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    @1
    @0
    cG
    co
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    isabli.1
    @2
    vx
    vy
    cX
    isabli.3
    rgen2a
    vx
    vy
    cG
    cX
    cG
    cX
    isabli.1
    isabli.2
    grporn
    isablo
    mpbir2an
end
