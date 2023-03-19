include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wne.mm"
include "w3a.mm"
include "cc.mm"
include "cv.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "addcl.mm"
include "adantl.mm"
include "cmul.mm"
include "mulcl.mm"
include "cc0.mm"
include "c1.mm"
include "cdiv.mm"
include "reccl.mm"
include "cneg.mm"
include "neg1cn.mm"
include "a1i.mm"
include "plyssc.mm"
include "simp1.mm"
include "sseldi.mm"
include "simp2.mm"
include "simp3.mm"
include "quotcl.mm"

theorem quotcl2
  let cS: class S
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let cR: class R


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) /\ G =/= 0p ) -> ( F quot G ) e. ( Poly ` CC ) )

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
    cG
    c0p
    wne
    #
    w3a
    #
    vx
    vy
    cc
    cF
    cG
    vx
    cv
    #
    cc
    wcel
    #
    vy
    cv
    #
    cc
    wcel
    wa
    #
    @5
    @7
    caddc
    co
    cc
    wcel
    @4
    @5
    @7
    addcl
    adantl
    @8
    @5
    @7
    cmul
    co
    cc
    wcel
    @4
    @5
    @7
    mulcl
    adantl
    @6
    @5
    cc0
    wne
    wa
    c1
    @5
    cdiv
    co
    cc
    wcel
    @4
    @5
    reccl
    adantl
    c1
    cneg
    cc
    wcel
    @4
    neg1cn
    a1i
    @4
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
    @3
    simp1
    sseldi
    @4
    @0
    @9
    cG
    @10
    @1
    @2
    @3
    simp2
    sseldi
    @1
    @2
    @3
    simp3
    quotcl
end
