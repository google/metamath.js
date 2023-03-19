include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "ci.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cr.mm"
include "imre.mm"
include "negicn.mm"
include "mulcl.mm"
include "mpan.mm"
include "recl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem imcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( Im ` A ) e. RR )

  proof
    cA
    cc
    wcel
    #
    cA
    cim
    cfv
    ci
    cneg
    #
    cA
    cmul
    co
    #
    cre
    cfv
    #
    cr
    cA
    imre
    @0
    @2
    cc
    wcel
    #
    @3
    cr
    wcel
    @1
    cc
    wcel
    @0
    @4
    negicn
    @1
    cA
    mulcl
    mpan
    @2
    recl
    syl
    eqeltrd
end
