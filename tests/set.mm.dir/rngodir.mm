include "crngo.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "rngoi.mm"
include "simprd.mm"
include "simpld.mm"
include "simp3.mm"
include "ralimi.mm"
include "2ralimi.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "rspc3v.mm"
include "syl5.mm"
include "mpan9.mm"

theorem rngodir
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


  assert |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) H C ) = ( ( A H C ) G ( B H C ) ) )

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
    @1
    @2
    @4
    cH
    co
    #
    cH
    co
    wceq
    #
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
    #
    @4
    cH
    co
    #
    @7
    @5
    cG
    co
    #
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
    #
    cA
    cB
    cG
    co
    #
    cC
    cH
    co
    #
    cA
    cC
    cH
    co
    #
    cB
    cC
    cH
    co
    #
    cG
    co
    #
    wceq
    #
    @0
    @15
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
    @15
    @23
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
    @15
    @12
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
    @16
    @22
    @14
    @24
    vx
    vy
    cX
    cX
    @13
    @12
    vz
    cX
    @6
    @8
    @12
    simp3
    ralimi
    2ralimi
    @12
    @22
    cA
    @2
    cG
    co
    #
    @4
    cH
    co
    #
    cA
    @4
    cH
    co
    #
    @5
    cG
    co
    #
    wceq
    @17
    @4
    cH
    co
    #
    @27
    cB
    @4
    cH
    co
    #
    cG
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
    @10
    @26
    @11
    @28
    @32
    @9
    @25
    @4
    cH
    @1
    cA
    @2
    cG
    oveq1
    oveq1d
    @32
    @7
    @27
    @5
    cG
    @1
    cA
    @4
    cH
    oveq1
    oveq1d
    eqeq12d
    @2
    cB
    wceq
    #
    @26
    @29
    @28
    @31
    @33
    @25
    @17
    @4
    cH
    @2
    cB
    cA
    cG
    oveq2
    oveq1d
    @33
    @5
    @30
    @27
    cG
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
    @29
    @18
    @31
    @21
    @4
    cC
    @17
    cH
    oveq2
    @34
    @27
    @19
    @30
    @20
    cG
    @4
    cC
    cA
    cH
    oveq2
    @4
    cC
    cB
    cH
    oveq2
    oveq12d
    eqeq12d
    rspc3v
    syl5
    mpan9
end
