include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "cz.mm"
include "crio.mm"
include "flval.mm"
include "wreu.mm"
include "rebtwnz.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem flcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. RR -> ( |_ ` A ) e. ZZ )

  proof
    cA
    cr
    wcel
    #
    cA
    cfl
    cfv
    vx
    cv
    #
    cA
    cle
    wbr
    cA
    @1
    c1
    caddc
    co
    clt
    wbr
    wa
    #
    vx
    cz
    crio
    #
    cz
    vx
    cA
    flval
    @0
    @2
    vx
    cz
    wreu
    @3
    cz
    wcel
    vx
    cA
    rebtwnz
    @2
    vx
    cz
    riotacl
    syl
    eqeltrd
end
