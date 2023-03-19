include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "plyssc.mm"
include "simpl.mm"
include "sseldi.mm"
include "simpr.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "addcl.mm"
include "adantl.mm"
include "cmul.mm"
include "mulcl.mm"
include "c1.mm"
include "cneg.mm"
include "neg1cn.mm"
include "a1i.mm"
include "plysub.mm"

theorem plysubcl
  let cS: class S
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( F oF - G ) e. ( Poly ` CC ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    vx
    vy
    cc
    cF
    cG
    @3
    @0
    cc
    cply
    cfv
    #
    cF
    cS
    plyssc
    #
    @1
    @2
    simpl
    sseldi
    @3
    @0
    @4
    cG
    @5
    @1
    @2
    simpr
    sseldi
    vx
    cv
    #
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    wa
    #
    @6
    @7
    caddc
    co
    cc
    wcel
    @3
    @6
    @7
    addcl
    adantl
    @8
    @6
    @7
    cmul
    co
    cc
    wcel
    @3
    @6
    @7
    mulcl
    adantl
    c1
    cneg
    cc
    wcel
    @3
    neg1cn
    a1i
    plysub
end
