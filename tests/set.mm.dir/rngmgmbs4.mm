include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "wfo.mm"
include "crn.mm"
include "r19.12.mm"
include "wcel.mm"
include "simpl.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "syl5.mm"
include "reximdv.mm"
include "ralimia.mm"
include "syl.mm"
include "anim2i.mm"
include "foov.mm"
include "sylibr.mm"
include "forn.mm"

theorem rngmgmbs4
  let vx: setvar x
  let vu: setvar u
  let cG: class G
  let cX: class X
  let vy: setvar y

  disjoint G u
  disjoint G x
  disjoint u x
  disjoint X u
  disjoint X x
  disjoint G y
  disjoint u y
  disjoint x y
  disjoint X y
  assert |- ( ( G : ( X X. X ) --> X /\ E. u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) -> ran G = X )

  proof
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    #
    @3
    wceq
    #
    @3
    @2
    cG
    co
    @3
    wceq
    #
    wa
    #
    vx
    cX
    wral
    vu
    cX
    wrex
    #
    wa
    #
    @0
    cX
    cG
    wfo
    #
    cG
    crn
    cX
    wceq
    @9
    @1
    @3
    @2
    vy
    cv
    #
    cG
    co
    #
    wceq
    #
    vy
    cX
    wrex
    #
    vu
    cX
    wrex
    #
    vx
    cX
    wral
    #
    wa
    @10
    @8
    @16
    @1
    @8
    @7
    vu
    cX
    wrex
    #
    vx
    cX
    wral
    @16
    @7
    vu
    vx
    cX
    cX
    r19.12
    @17
    @15
    vx
    cX
    @3
    cX
    wcel
    #
    @7
    @14
    vu
    cX
    @7
    @3
    @4
    wceq
    #
    @18
    @14
    @7
    @4
    @3
    @5
    @6
    simpl
    eqcomd
    @18
    @19
    @14
    @13
    @19
    vy
    @3
    cX
    @11
    @3
    wceq
    @12
    @4
    @3
    @11
    @3
    @2
    cG
    oveq2
    eqeq2d
    rspcev
    ex
    syl5
    reximdv
    ralimia
    syl
    anim2i
    vu
    vy
    vx
    cX
    cX
    cX
    cG
    foov
    sylibr
    @0
    cX
    cG
    forn
    syl
end
