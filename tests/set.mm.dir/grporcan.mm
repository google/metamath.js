include "cgr.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "cv.mm"
include "cgi.mm"
include "cfv.mm"
include "wrex.mm"
include "wi.mm"
include "eqid.mm"
include "grpoidinv2.mm"
include "simpr.mm"
include "reximi.mm"
include "adantl.mm"
include "syl.mm"
include "ad2ant2rl.mm"
include "oveq1.mm"
include "ad2antll.mm"
include "grpoass.mm"
include "3anassrs.mm"
include "adantlrl.mm"
include "adantrr.mm"
include "3exp2.mm"
include "imp42.mm"
include "adantllr.mm"
include "3eqtr3d.mm"
include "adantrrl.mm"
include "oveq2.mm"
include "ad2antrl.mm"
include "grporid.mm"
include "ad2antrr.mm"
include "ad2ant2r.mm"
include "adantr.mm"
include "exp45.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "impbid1.mm"
include "exp43.mm"
include "3imp2.mm"

theorem grporcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cX: class X
  let vy: setvar y
  assume grprcan.1: |- X = ran G


  assert |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G C ) = ( B G C ) <-> A = B ) )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    cA
    cC
    cG
    co
    #
    cB
    cC
    cG
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wb
    #
    @0
    @1
    @2
    @3
    @8
    @0
    @1
    wa
    #
    @2
    @3
    wa
    #
    wa
    #
    @6
    @7
    @11
    cC
    vy
    cv
    #
    cG
    co
    #
    cG
    cgi
    cfv
    #
    wceq
    #
    vy
    cX
    wrex
    #
    @6
    @7
    wi
    #
    @0
    @3
    @16
    @1
    @2
    @0
    @3
    wa
    @14
    cC
    cG
    co
    cC
    wceq
    cC
    @14
    cG
    co
    cC
    wceq
    wa
    #
    @12
    cC
    cG
    co
    @14
    wceq
    #
    @15
    wa
    #
    vy
    cX
    wrex
    #
    wa
    @16
    vy
    cC
    @14
    cG
    cX
    grprcan.1
    @14
    eqid
    #
    grpoidinv2
    @21
    @16
    @18
    @20
    @15
    vy
    cX
    @19
    @15
    simpr
    reximi
    adantl
    syl
    ad2ant2rl
    @11
    @15
    @17
    vy
    cX
    @11
    @12
    cX
    wcel
    #
    @15
    @6
    @7
    @11
    @23
    @15
    @6
    wa
    wa
    #
    wa
    #
    cA
    @14
    cG
    co
    #
    cB
    @14
    cG
    co
    #
    cA
    cB
    @25
    cA
    @13
    cG
    co
    #
    cB
    @13
    cG
    co
    #
    @26
    @27
    @11
    @23
    @6
    @28
    @29
    wceq
    @15
    @11
    @23
    @6
    wa
    wa
    @4
    @12
    cG
    co
    #
    @5
    @12
    cG
    co
    #
    @28
    @29
    @6
    @30
    @31
    wceq
    @11
    @23
    @4
    @5
    @12
    cG
    oveq1
    ad2antll
    @11
    @23
    @30
    @28
    wceq
    #
    @6
    @9
    @3
    @23
    @32
    @2
    @0
    @1
    @3
    @23
    @32
    cA
    cC
    @12
    cG
    cX
    grprcan.1
    grpoass
    3anassrs
    adantlrl
    adantrr
    @11
    @23
    @31
    @29
    wceq
    #
    @6
    @0
    @10
    @23
    @33
    @1
    @0
    @2
    @3
    @23
    @33
    @0
    @2
    @3
    @23
    @33
    cB
    cC
    @12
    cG
    cX
    grprcan.1
    grpoass
    3exp2
    imp42
    adantllr
    adantrr
    3eqtr3d
    adantrrl
    @24
    @28
    @26
    wceq
    #
    @11
    @15
    @34
    @23
    @6
    @13
    @14
    cA
    cG
    oveq2
    ad2antrl
    adantl
    @24
    @29
    @27
    wceq
    #
    @11
    @15
    @35
    @23
    @6
    @13
    @14
    cB
    cG
    oveq2
    ad2antrl
    adantl
    3eqtr3d
    @9
    @26
    cA
    wceq
    @10
    @24
    cA
    @14
    cG
    cX
    grprcan.1
    @22
    grporid
    ad2antrr
    @11
    @27
    cB
    wceq
    #
    @24
    @0
    @2
    @36
    @1
    @3
    cB
    @14
    cG
    cX
    grprcan.1
    @22
    grporid
    ad2ant2r
    adantr
    3eqtr3d
    exp45
    rexlimdv
    mpd
    cA
    cB
    cC
    cG
    oveq1
    impbid1
    exp43
    3imp2
end
