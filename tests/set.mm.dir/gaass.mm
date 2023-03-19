include "wcel.mm"
include "w3a.mm"
include "cga.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "c0g.mm"
include "cfv.mm"
include "wa.mm"
include "cxp.mm"
include "wf.mm"
include "cgrp.mm"
include "cvv.mm"
include "eqid.mm"
include "isga.mm"
include "simprbi.mm"
include "simprd.mm"
include "simpr.mm"
include "ralimi.mm"
include "syl.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "rspc3v.mm"
include "syl5.mm"
include "3coml.mm"
include "impcom.mm"

theorem gaass
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gaass.1: |- X = ( Base ` G )
  assume gaass.2: |- .+ = ( +g ` G )


  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ ( A e. X /\ B e. X /\ C e. Y ) ) -> ( ( A .+ B ) .(+) C ) = ( A .(+) ( B .(+) C ) ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cY
    wcel
    #
    w3a
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cA
    cB
    c.pl
    co
    #
    cC
    c.po
    co
    #
    cA
    cB
    cC
    c.po
    co
    #
    c.po
    co
    #
    wceq
    #
    @2
    @0
    @1
    @3
    @8
    wi
    @3
    vy
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    vx
    cv
    #
    c.po
    co
    #
    @9
    @10
    @12
    c.po
    co
    #
    c.po
    co
    #
    wceq
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    vx
    cY
    wral
    #
    @2
    @0
    @1
    w3a
    @8
    @3
    cG
    c0g
    cfv
    #
    @12
    c.po
    co
    @12
    wceq
    #
    @17
    wa
    #
    vx
    cY
    wral
    #
    @18
    @3
    cX
    cY
    cxp
    cY
    c.po
    wf
    #
    @22
    @3
    cG
    cgrp
    wcel
    cY
    cvv
    wcel
    wa
    @23
    @22
    wa
    vx
    vy
    vz
    c.pl
    c.po
    cG
    cX
    cY
    @19
    gaass.1
    gaass.2
    @19
    eqid
    isga
    simprbi
    simprd
    @21
    @17
    vx
    cY
    @20
    @17
    simpr
    ralimi
    syl
    @16
    @8
    @11
    cC
    c.po
    co
    #
    @9
    @10
    cC
    c.po
    co
    #
    c.po
    co
    #
    wceq
    cA
    @10
    c.pl
    co
    #
    cC
    c.po
    co
    #
    cA
    @25
    c.po
    co
    #
    wceq
    vx
    vy
    vz
    cC
    cA
    cB
    cY
    cX
    cX
    @12
    cC
    wceq
    #
    @13
    @24
    @15
    @26
    @12
    cC
    @11
    c.po
    oveq2
    @30
    @14
    @25
    @9
    c.po
    @12
    cC
    @10
    c.po
    oveq2
    oveq2d
    eqeq12d
    @9
    cA
    wceq
    #
    @24
    @28
    @26
    @29
    @31
    @11
    @27
    cC
    c.po
    @9
    cA
    @10
    c.pl
    oveq1
    oveq1d
    @9
    cA
    @25
    c.po
    oveq1
    eqeq12d
    @10
    cB
    wceq
    #
    @28
    @5
    @29
    @7
    @32
    @27
    @4
    cC
    c.po
    @10
    cB
    cA
    c.pl
    oveq2
    oveq1d
    @32
    @25
    @6
    cA
    c.po
    @10
    cB
    cC
    c.po
    oveq1
    oveq2d
    eqeq12d
    rspc3v
    syl5
    3coml
    impcom
end
