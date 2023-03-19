include "cc.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "crio.mm"
include "sqrtval.mm"
include "wreu.mm"
include "sqreu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem sqrtcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( sqrt ` A ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cA
    csqrt
    cfv
    vx
    cv
    #
    c2
    cexp
    co
    cA
    wceq
    cc0
    @1
    cre
    cfv
    cle
    wbr
    ci
    @1
    cmul
    co
    crp
    wnel
    w3a
    #
    vx
    cc
    crio
    #
    cc
    vx
    cA
    sqrtval
    @0
    @2
    vx
    cc
    wreu
    @3
    cc
    wcel
    vx
    cA
    sqreu
    @2
    vx
    cc
    riotacl
    syl
    eqeltrd
end
