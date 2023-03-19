include "crngo.mm"
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
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "w3a.mm"
include "rngoi.mm"
include "simprrd.mm"
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
include "jctir.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "reu4.mm"
include "sylibr.mm"

theorem rngoideu
  let vx: setvar x
  let vu: setvar u
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume ringi.1: |- G = ( 1st ` R )
  assume ringi.2: |- H = ( 2nd ` R )
  assume ringi.3: |- X = ran G

  disjoint u x
  disjoint G u
  disjoint G x
  disjoint H u
  disjoint H x
  disjoint X u
  disjoint X x
  disjoint R u
  disjoint R x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint H y
  disjoint H z
  disjoint X y
  disjoint X z
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  assert |- ( R e. RingOps -> E! u e. X A. x e. X ( ( u H x ) = x /\ ( x H u ) = x ) )

  proof
    cR
    crngo
    wcel
    #
    vu
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    @2
    wceq
    #
    @2
    @1
    cH
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
    #
    @8
    vy
    cv
    #
    @2
    cH
    co
    #
    @2
    wceq
    #
    @2
    @10
    cH
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
    wa
    @8
    vu
    cX
    wreu
    @0
    @9
    @20
    @0
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
    @3
    @10
    cH
    co
    @1
    @13
    cH
    co
    wceq
    @1
    @2
    @10
    cG
    co
    cH
    co
    @3
    @1
    @10
    cH
    co
    #
    cG
    co
    wceq
    @1
    @2
    cG
    co
    @10
    cH
    co
    @21
    @13
    cG
    co
    wceq
    w3a
    vy
    cX
    wral
    vx
    cX
    wral
    vu
    cX
    wral
    @9
    vu
    vx
    vy
    cR
    cG
    cH
    cX
    ringi.1
    ringi.2
    ringi.3
    rngoi
    simprrd
    @19
    vu
    vy
    cX
    @1
    cX
    wcel
    #
    @10
    cX
    wcel
    #
    wa
    @17
    @21
    @10
    wceq
    #
    @21
    @1
    wceq
    #
    wa
    #
    @18
    @23
    @8
    @24
    @22
    @16
    @25
    @8
    @4
    vx
    cX
    wral
    @23
    @24
    @7
    @4
    vx
    cX
    @4
    @6
    simpl
    ralimi
    @4
    @24
    vx
    @10
    cX
    vx
    vy
    weq
    #
    @3
    @21
    @2
    @10
    @2
    @10
    @1
    cH
    oveq2
    @27
    id
    eqeq12d
    rspcv
    syl5
    @16
    @14
    vx
    cX
    wral
    @22
    @25
    @15
    @14
    vx
    cX
    @12
    @14
    simpr
    ralimi
    @14
    @25
    vx
    @1
    cX
    vx
    vu
    weq
    #
    @13
    @21
    @2
    @1
    @2
    @1
    @10
    cH
    oveq1
    @28
    id
    eqeq12d
    rspcv
    syl5
    im2anan9r
    @26
    @10
    @1
    @21
    @10
    @1
    eqtr2
    eqcomd
    syl6
    rgen2a
    jctir
    @8
    @16
    vu
    vy
    cX
    @18
    @7
    @15
    vx
    cX
    @18
    @4
    @12
    @6
    @14
    @18
    @3
    @11
    @2
    @1
    @10
    @2
    cH
    oveq1
    eqeq1d
    @18
    @5
    @13
    @2
    @1
    @10
    @2
    cH
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    reu4
    sylibr
end
