include "csubrg.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "wcel.mm"
include "csubg.mm"
include "cur.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "subrgsubg.mm"
include "ssriv.mm"
include "sstr.mm"
include "mpan2.mm"
include "subgint.mm"
include "sylan.mm"
include "ssel2.mm"
include "adantlr.mm"
include "eqid.mm"
include "subrg1cl.mm"
include "syl.mm"
include "ralrimiva.mm"
include "fvex.mm"
include "elint2.mm"
include "sylibr.mm"
include "simprl.mm"
include "elinti.mm"
include "imp.mm"
include "simprr.mm"
include "subrgmcl.mm"
include "syl3anc.mm"
include "ovex.mm"
include "ralrimivva.mm"
include "crg.mm"
include "w3a.mm"
include "wb.mm"
include "ssn0.mm"
include "wex.mm"
include "n0.mm"
include "subrgrcl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "cbs.mm"
include "issubrg2.mm"
include "3syl.mm"
include "mpbir3and.mm"

theorem subrgint
  let cR: class R
  let cS: class S
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( S C_ ( SubRing ` R ) /\ S =/= (/) ) -> |^| S e. ( SubRing ` R ) )

  proof
    cS
    cR
    csubrg
    cfv
    #
    wss
    #
    cS
    c0
    wne
    #
    wa
    #
    cS
    cint
    #
    @0
    wcel
    #
    @4
    cR
    csubg
    cfv
    #
    wcel
    #
    cR
    cur
    cfv
    #
    @4
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @4
    wcel
    #
    vy
    @4
    wral
    vx
    @4
    wral
    #
    @1
    cS
    @6
    wss
    #
    @2
    @7
    @1
    @0
    @6
    wss
    @16
    vr
    @0
    @6
    vr
    cv
    #
    cR
    subrgsubg
    ssriv
    cS
    @0
    @6
    sstr
    mpan2
    cS
    cR
    subgint
    sylan
    @3
    @8
    @17
    wcel
    #
    vr
    cS
    wral
    @9
    @3
    @18
    vr
    cS
    @3
    @17
    cS
    wcel
    #
    wa
    @17
    @0
    wcel
    #
    @18
    @1
    @19
    @20
    @2
    cS
    @0
    @17
    ssel2
    adantlr
    #
    @17
    cR
    @8
    @8
    eqid
    #
    subrg1cl
    syl
    ralrimiva
    vr
    @8
    cS
    cR
    cur
    fvex
    elint2
    sylibr
    @3
    @14
    vx
    vy
    @4
    @4
    @3
    @10
    @4
    wcel
    #
    @11
    @4
    wcel
    #
    wa
    #
    wa
    #
    @13
    @17
    wcel
    #
    vr
    cS
    wral
    @14
    @26
    @27
    vr
    cS
    @26
    @19
    wa
    @20
    @10
    @17
    wcel
    #
    @11
    @17
    wcel
    #
    @27
    @3
    @19
    @20
    @25
    @21
    adantlr
    @26
    @23
    @19
    @28
    @3
    @23
    @24
    simprl
    @23
    @19
    @28
    @10
    cS
    @17
    elinti
    imp
    sylan
    @26
    @24
    @19
    @29
    @3
    @23
    @24
    simprr
    @24
    @19
    @29
    @11
    cS
    @17
    elinti
    imp
    sylan
    @17
    cR
    @12
    @10
    @11
    @12
    eqid
    #
    subrgmcl
    syl3anc
    ralrimiva
    vr
    @13
    cS
    @10
    @11
    @12
    ovex
    elint2
    sylibr
    ralrimivva
    @3
    @0
    c0
    wne
    #
    cR
    crg
    wcel
    #
    @5
    @7
    @9
    @15
    w3a
    wb
    cS
    @0
    ssn0
    @31
    @20
    vr
    wex
    @32
    vr
    @0
    n0
    @20
    @32
    vr
    @17
    cR
    subrgrcl
    exlimiv
    sylbi
    vx
    vy
    @4
    cR
    cbs
    cfv
    #
    cR
    @12
    @8
    @33
    eqid
    @22
    @30
    issubrg2
    3syl
    mpbir3and
end
