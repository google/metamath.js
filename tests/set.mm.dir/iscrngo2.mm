include "ccring.mm"
include "wcel.mm"
include "crngo.mm"
include "ccm2.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "iscrngo.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wb.mm"
include "wrel.mm"
include "relrngo.mm"
include "1st2nd.mm"
include "mpan.mm"
include "eleq1.mm"
include "crn.mm"
include "rneqi.mm"
include "eqtri.mm"
include "raleqi.mm"
include "oveqi.mm"
include "eqeq12i.mm"
include "raleqbii.mm"
include "ralbii.mm"
include "cvv.mm"
include "fvex.mm"
include "iscom2.mm"
include "mp2an.mm"
include "3bitr4ri.mm"
include "syl6bb.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem iscrngo2
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  assume iscring2.1: |- G = ( 1st ` R )
  assume iscring2.2: |- H = ( 2nd ` R )
  assume iscring2.3: |- X = ran G

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint X x
  disjoint X y
  assert |- ( R e. CRingOps <-> ( R e. RingOps /\ A. x e. X A. y e. X ( x H y ) = ( y H x ) ) )

  proof
    cR
    ccring
    wcel
    cR
    crngo
    wcel
    #
    cR
    ccm2
    wcel
    #
    wa
    @0
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    @3
    @2
    cH
    co
    #
    wceq
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    wa
    cR
    iscrngo
    @0
    @1
    @8
    @0
    cR
    cR
    c1st
    cfv
    #
    cR
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @1
    @8
    wb
    crngo
    wrel
    @0
    @12
    relrngo
    cR
    crngo
    1st2nd
    mpan
    @12
    @1
    @11
    ccm2
    wcel
    #
    @8
    cR
    @11
    ccm2
    eleq1
    @2
    @3
    @10
    co
    #
    @3
    @2
    @10
    co
    #
    wceq
    #
    vy
    @9
    crn
    #
    wral
    #
    vx
    cX
    wral
    @18
    vx
    @17
    wral
    #
    @8
    @13
    @18
    vx
    cX
    @17
    cX
    cG
    crn
    @17
    iscring2.3
    cG
    @9
    iscring2.1
    rneqi
    eqtri
    #
    raleqi
    @7
    @18
    vx
    cX
    @6
    @16
    vy
    cX
    @17
    @20
    @4
    @14
    @5
    @15
    cH
    @10
    @2
    @3
    iscring2.2
    oveqi
    cH
    @10
    @3
    @2
    iscring2.2
    oveqi
    eqeq12i
    raleqbii
    ralbii
    @9
    cvv
    wcel
    @10
    cvv
    wcel
    @13
    @19
    wb
    cR
    c1st
    fvex
    cR
    c2nd
    fvex
    cvv
    cvv
    @9
    @10
    vx
    vy
    iscom2
    mp2an
    3bitr4ri
    syl6bb
    syl
    pm5.32i
    bitri
end
