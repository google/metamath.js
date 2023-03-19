include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wne.mm"
include "w3a.mm"
include "cquot.mm"
include "co.mm"
include "cc.mm"
include "wceq.mm"
include "cdgr.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cv.mm"
include "wa.mm"
include "caddc.mm"
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
include "quotlem.mm"
include "simprd.mm"

theorem quotdgr
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  assume quotdgr.1: |- R = ( F oF - ( G oF x. ( F quot G ) ) )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) /\ G =/= 0p ) -> ( R = 0p \/ ( deg ` R ) < ( deg ` G ) ) )

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
    cF
    cG
    cquot
    co
    cc
    cply
    cfv
    #
    wcel
    cR
    c0p
    wceq
    cR
    cdgr
    cfv
    cG
    cdgr
    cfv
    clt
    wbr
    wo
    @4
    vx
    vy
    cR
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
    @6
    @8
    caddc
    co
    cc
    wcel
    @4
    @6
    @8
    addcl
    adantl
    @9
    @6
    @8
    cmul
    co
    cc
    wcel
    @4
    @6
    @8
    mulcl
    adantl
    @7
    @6
    cc0
    wne
    wa
    c1
    @6
    cdiv
    co
    cc
    wcel
    @4
    @6
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
    @5
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
    @5
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
    quotdgr.1
    quotlem
    simprd
end
