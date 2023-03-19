include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wreu.mm"
include "isexid2.mm"
include "simpl.mm"
include "ralimi.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "syl5.mm"
include "simpr.mm"
include "oveq1.mm"
include "im2anan9r.mm"
include "eqtr2.mm"
include "eqcomd.mm"
include "syl6.mm"
include "rgen2a.mm"
include "a1i.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem exidu1
  let vx: setvar x
  let vu: setvar u
  let cG: class G
  let cX: class X
  let vy: setvar y
  assume exidu1.1: |- X = ran G

  disjoint G u
  disjoint G x
  disjoint u x
  disjoint X u
  disjoint X x
  disjoint G y
  disjoint u y
  disjoint x y
  disjoint X y
  assert |- ( G e. ( Magma i^i ExId ) -> E! u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) )

  proof
    cG
    cmagm
    cexid
    cin
    wcel
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
    @2
    wceq
    #
    @2
    @1
    cG
    co
    #
    @2
    wceq
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    wrex
    @8
    vy
    cv
    #
    @2
    cG
    co
    #
    @2
    wceq
    #
    @2
    @9
    cG
    co
    #
    @2
    wceq
    #
    wa
    #
    vx
    cX
    wral
    #
    wa
    #
    vu
    vy
    weq
    #
    wi
    #
    vy
    cX
    wral
    vu
    cX
    wral
    #
    @8
    vu
    cX
    wreu
    vx
    vu
    cG
    cX
    exidu1.1
    isexid2
    @19
    @0
    @18
    vu
    vy
    cX
    @1
    cX
    wcel
    #
    @9
    cX
    wcel
    #
    wa
    @16
    @1
    @9
    cG
    co
    #
    @9
    wceq
    #
    @22
    @1
    wceq
    #
    wa
    #
    @17
    @21
    @8
    @23
    @20
    @15
    @24
    @8
    @4
    vx
    cX
    wral
    @21
    @23
    @7
    @4
    vx
    cX
    @4
    @6
    simpl
    ralimi
    @4
    @23
    vx
    @9
    cX
    vx
    vy
    weq
    #
    @3
    @22
    @2
    @9
    @2
    @9
    @1
    cG
    oveq2
    @26
    id
    eqeq12d
    rspcv
    syl5
    @15
    @13
    vx
    cX
    wral
    @20
    @24
    @14
    @13
    vx
    cX
    @11
    @13
    simpr
    ralimi
    @13
    @24
    vx
    @1
    cX
    vx
    vu
    weq
    #
    @12
    @22
    @2
    @1
    @2
    @1
    @9
    cG
    oveq1
    @27
    id
    eqeq12d
    rspcv
    syl5
    im2anan9r
    @25
    @9
    @1
    @22
    @9
    @1
    eqtr2
    eqcomd
    syl6
    rgen2a
    a1i
    @8
    @15
    vu
    vy
    cX
    @17
    @7
    @14
    vx
    cX
    @17
    @4
    @11
    @6
    @13
    @17
    @3
    @10
    @2
    @1
    @9
    @2
    cG
    oveq1
    eqeq1d
    @17
    @5
    @12
    @2
    @1
    @9
    @2
    cG
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    reu4
    sylanbrc
end
