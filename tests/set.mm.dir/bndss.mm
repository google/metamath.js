include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "cxp.mm"
include "cres.mm"
include "cbnd.mm"
include "metres2.mm"
include "adantlr.mm"
include "wi.mm"
include "ssel2.mm"
include "ancoms.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "sylan.mm"
include "adantlll.mm"
include "cin.mm"
include "dfss.mm"
include "biimpi.mm"
include "incom.mm"
include "syl6eq.mm"
include "ineq1.mm"
include "sylan9eq.mm"
include "adantll.mm"
include "eqid.mm"
include "blssp.mm"
include "an4s.mm"
include "anassrs.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "ex.mm"
include "reximdva.mm"
include "imp.mm"
include "syldan.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "jca.mm"
include "isbnd.mm"
include "anbi1i.mm"
include "3imtr4i.mm"

theorem bndss
  let cS: class S
  let cM: class M
  let cX: class X
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cP: class P
  let cR: class R
  let cY: class Y


  assert |- ( ( M e. ( Bnd ` X ) /\ S C_ X ) -> ( M |` ( S X. S ) ) e. ( Bnd ` S ) )

  proof
    cM
    cX
    cme
    cfv
    wcel
    #
    cX
    vy
    cv
    #
    vr
    cv
    #
    cM
    cbl
    cfv
    #
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    vy
    cX
    wral
    #
    wa
    #
    cS
    cX
    wss
    #
    wa
    #
    cM
    cS
    cS
    cxp
    cres
    #
    cS
    cme
    cfv
    wcel
    #
    cS
    vx
    cv
    #
    @2
    @11
    cbl
    cfv
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    vx
    cS
    wral
    #
    wa
    cM
    cX
    cbnd
    cfv
    wcel
    #
    @9
    wa
    @11
    cS
    cbnd
    cfv
    wcel
    @10
    @12
    @17
    @0
    @9
    @12
    @7
    cM
    cS
    cX
    metres2
    adantlr
    @10
    @16
    vx
    cS
    @8
    @13
    cS
    wcel
    #
    @9
    @16
    @8
    @19
    wa
    @9
    @16
    @0
    @19
    @7
    @9
    @16
    wi
    @0
    @19
    wa
    #
    @7
    wa
    @9
    @16
    @20
    @9
    @7
    @16
    @20
    @9
    wa
    #
    @7
    cX
    @13
    @2
    @3
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    @16
    @19
    @9
    @7
    @24
    @0
    @19
    @9
    wa
    @13
    cX
    wcel
    #
    @7
    @24
    @9
    @19
    @25
    cS
    cX
    @13
    ssel2
    ancoms
    @6
    @24
    vy
    @13
    cX
    @1
    @13
    wceq
    #
    @5
    @23
    vr
    crp
    @26
    @4
    @22
    cX
    @1
    @13
    @2
    @3
    oveq1
    eqeq2d
    rexbidv
    rspcva
    sylan
    adantlll
    @21
    @24
    @16
    @21
    @23
    @15
    vr
    crp
    @21
    @2
    crp
    wcel
    #
    wa
    #
    @23
    @15
    @28
    @23
    wa
    cS
    @22
    cS
    cin
    #
    @14
    @21
    @23
    cS
    @29
    wceq
    #
    @27
    @9
    @23
    @30
    @20
    @9
    @23
    cS
    cX
    cS
    cin
    #
    @29
    @9
    cS
    cS
    cX
    cin
    #
    @31
    @9
    cS
    @32
    wceq
    cS
    cX
    dfss
    biimpi
    cS
    cX
    incom
    syl6eq
    cX
    @22
    cS
    ineq1
    sylan9eq
    adantll
    adantlr
    @28
    @14
    @29
    wceq
    #
    @23
    @20
    @9
    @27
    @33
    @0
    @9
    @19
    @27
    @33
    @2
    cS
    cM
    @11
    cX
    @13
    @11
    eqid
    blssp
    an4s
    anassrs
    adantr
    eqtr4d
    ex
    reximdva
    imp
    syldan
    an32s
    ex
    an32s
    imp
    an32s
    ralrimiva
    jca
    @18
    @8
    @9
    vy
    cM
    cX
    vr
    isbnd
    anbi1i
    vx
    @11
    cS
    vr
    isbnd
    3imtr4i
end
