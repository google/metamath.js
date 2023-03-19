include "crngo.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "wrex.mm"
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "rngoi.mm"
include "simprd.mm"
include "simpld.mm"
include "simp1.mm"
include "ralimi.mm"
include "2ralimi.mm"
include "syl.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem rngoass
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ringi.1: |- G = ( 1st ` R )
  assume ringi.2: |- H = ( 2nd ` R )
  assume ringi.3: |- X = ran G


  assert |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A H B ) H C ) = ( A H ( B H C ) ) )

  proof
    cR
    crngo
    wcel
    #
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
    #
    @1
    @2
    @4
    cH
    co
    #
    cH
    co
    #
    wceq
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    cB
    cX
    wcel
    cC
    cX
    wcel
    w3a
    cA
    cB
    cH
    co
    #
    cC
    cH
    co
    #
    cA
    cB
    cC
    cH
    co
    #
    cH
    co
    #
    wceq
    #
    @0
    @8
    @1
    @2
    @4
    cG
    co
    cH
    co
    @3
    @1
    @4
    cH
    co
    #
    cG
    co
    wceq
    #
    @1
    @2
    cG
    co
    @4
    cH
    co
    @16
    @6
    cG
    co
    wceq
    #
    w3a
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @10
    @0
    @21
    @3
    @2
    wceq
    @2
    @1
    cH
    co
    @2
    wceq
    wa
    vy
    cX
    wral
    vx
    cX
    wrex
    #
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
    @21
    @22
    wa
    vx
    vy
    vz
    cR
    cG
    cH
    cX
    ringi.1
    ringi.2
    ringi.3
    rngoi
    simprd
    simpld
    @20
    @9
    vx
    vy
    cX
    cX
    @19
    @8
    vz
    cX
    @8
    @17
    @18
    simp1
    ralimi
    2ralimi
    syl
    @8
    @15
    cA
    @2
    cH
    co
    #
    @4
    cH
    co
    #
    cA
    @6
    cH
    co
    #
    wceq
    @11
    @4
    cH
    co
    #
    cA
    cB
    @4
    cH
    co
    #
    cH
    co
    #
    wceq
    vx
    vy
    vz
    cA
    cB
    cC
    cX
    cX
    cX
    @1
    cA
    wceq
    #
    @5
    @24
    @7
    @25
    @29
    @3
    @23
    @4
    cH
    @1
    cA
    @2
    cH
    oveq1
    oveq1d
    @1
    cA
    @6
    cH
    oveq1
    eqeq12d
    @2
    cB
    wceq
    #
    @24
    @26
    @25
    @28
    @30
    @23
    @11
    @4
    cH
    @2
    cB
    cA
    cH
    oveq2
    oveq1d
    @30
    @6
    @27
    cA
    cH
    @2
    cB
    @4
    cH
    oveq1
    oveq2d
    eqeq12d
    @4
    cC
    wceq
    #
    @26
    @12
    @28
    @14
    @4
    cC
    @11
    cH
    oveq2
    @31
    @27
    @13
    cA
    cH
    @4
    cC
    cB
    cH
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    mpan9
end
