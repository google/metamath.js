include "crngo.mm"
include "wcel.mm"
include "cop.mm"
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wral.mm"
include "wrex.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wrel.mm"
include "relrngo.mm"
include "1st2nd.mm"
include "mpan.mm"
include "opeq12i.mm"
include "syl6reqr.mm"
include "id.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "isrngo.mm"
include "ax-mp.mm"
include "sylib.mm"

theorem rngoi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  assume ringi.1: |- G = ( 1st ` R )
  assume ringi.2: |- H = ( 2nd ` R )
  assume ringi.3: |- X = ran G

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint R x
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint H u
  disjoint X u
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint R u
  assert |- ( R e. RingOps -> ( ( G e. AbelOp /\ H : ( X X. X ) --> X ) /\ ( A. x e. X A. y e. X A. z e. X ( ( ( x H y ) H z ) = ( x H ( y H z ) ) /\ ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) /\ ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) ) /\ E. x e. X A. y e. X ( ( x H y ) = y /\ ( y H x ) = y ) ) ) )

  proof
    cR
    crngo
    wcel
    #
    cG
    cH
    cop
    #
    crngo
    wcel
    #
    cG
    cablo
    wcel
    cX
    cX
    cxp
    cX
    cH
    wf
    wa
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    vz
    cv
    #
    cH
    co
    @3
    @4
    @6
    cH
    co
    #
    cH
    co
    wceq
    @3
    @4
    @6
    cG
    co
    cH
    co
    @5
    @3
    @6
    cH
    co
    #
    cG
    co
    wceq
    @3
    @4
    cG
    co
    @6
    cH
    co
    @8
    @7
    cG
    co
    wceq
    w3a
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cX
    wral
    @5
    @4
    wceq
    @4
    @3
    cH
    co
    @4
    wceq
    wa
    vy
    cX
    wral
    vx
    cX
    wrex
    wa
    wa
    #
    @0
    @1
    cR
    crngo
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
    @1
    crngo
    wrel
    @0
    cR
    @12
    wceq
    relrngo
    cR
    crngo
    1st2nd
    mpan
    cG
    @10
    cH
    @11
    ringi.1
    ringi.2
    opeq12i
    syl6reqr
    @0
    id
    eqeltrd
    cH
    cvv
    wcel
    @2
    @9
    wb
    cH
    @11
    cvv
    ringi.2
    cR
    c2nd
    fvex
    eqeltri
    vx
    vy
    vz
    cvv
    cG
    cH
    cX
    ringi.3
    isrngo
    ax-mp
    sylib
end
