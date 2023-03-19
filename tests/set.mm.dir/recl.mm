include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "ccj.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cr.mm"
include "reval.mm"
include "ci.mm"
include "cmin.mm"
include "cmul.mm"
include "cjth.mm"
include "simpld.mm"
include "rehalfcld.mm"
include "eqeltrd.mm"

theorem recl
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( Re ` A ) e. RR )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    cA
    cA
    ccj
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    cr
    cA
    reval
    @0
    @2
    @0
    @2
    cr
    wcel
    ci
    cA
    @1
    cmin
    co
    cmul
    co
    cr
    wcel
    cA
    cjth
    simpld
    rehalfcld
    eqeltrd
end
