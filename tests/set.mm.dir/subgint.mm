include "csubg.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "wcel.mm"
include "cbs.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "cuni.mm"
include "intssuni.mm"
include "adantl.mm"
include "ssel2.mm"
include "adantlr.mm"
include "eqid.mm"
include "subgss.mm"
include "syl.mm"
include "ralrimiva.mm"
include "unissb.mm"
include "sylibr.mm"
include "sstrd.mm"
include "c0g.mm"
include "subg0cl.mm"
include "fvex.mm"
include "elint2.mm"
include "ne0i.mm"
include "simprl.mm"
include "elinti.mm"
include "imp.mm"
include "sylan.mm"
include "simprr.mm"
include "subgcl.mm"
include "syl3anc.mm"
include "ovex.mm"
include "anassrs.mm"
include "adantll.mm"
include "subginvcl.mm"
include "syl2anc.mm"
include "jca.mm"
include "cgrp.mm"
include "w3a.mm"
include "wb.mm"
include "ssn0.mm"
include "wex.mm"
include "n0.mm"
include "subgrcl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "issubg2.mm"
include "3syl.mm"
include "mpbir3and.mm"

theorem subgint
  let cS: class S
  let cG: class G
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( S C_ ( SubGrp ` G ) /\ S =/= (/) ) -> |^| S e. ( SubGrp ` G ) )

  proof
    cS
    cG
    csubg
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
    cG
    cbs
    cfv
    #
    wss
    #
    @4
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
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
    #
    @9
    cG
    cminusg
    cfv
    #
    cfv
    #
    @4
    wcel
    #
    wa
    #
    vx
    @4
    wral
    #
    @3
    @4
    cS
    cuni
    #
    @6
    @2
    @4
    @20
    wss
    @1
    cS
    intssuni
    adantl
    @3
    vg
    cv
    #
    @6
    wss
    #
    vg
    cS
    wral
    @20
    @6
    wss
    @3
    @22
    vg
    cS
    @3
    @21
    cS
    wcel
    #
    wa
    #
    @21
    @0
    wcel
    #
    @22
    @1
    @23
    @25
    @2
    cS
    @0
    @21
    ssel2
    adantlr
    #
    @6
    @21
    cG
    @6
    eqid
    #
    subgss
    syl
    ralrimiva
    vg
    cS
    @6
    unissb
    sylibr
    sstrd
    @3
    cG
    c0g
    cfv
    #
    @4
    wcel
    #
    @8
    @3
    @28
    @21
    wcel
    #
    vg
    cS
    wral
    @29
    @3
    @30
    vg
    cS
    @24
    @25
    @30
    @26
    @21
    cG
    @28
    @28
    eqid
    subg0cl
    syl
    ralrimiva
    vg
    @28
    cS
    cG
    c0g
    fvex
    elint2
    sylibr
    @4
    @28
    ne0i
    syl
    @3
    @18
    vx
    @4
    @3
    @9
    @4
    wcel
    #
    wa
    #
    @14
    @17
    @32
    @13
    vy
    @4
    @3
    @31
    @10
    @4
    wcel
    #
    @13
    @3
    @31
    @33
    wa
    #
    wa
    #
    @12
    @21
    wcel
    #
    vg
    cS
    wral
    @13
    @35
    @36
    vg
    cS
    @35
    @23
    wa
    @25
    @9
    @21
    wcel
    #
    @10
    @21
    wcel
    #
    @36
    @3
    @23
    @25
    @34
    @26
    adantlr
    @35
    @31
    @23
    @37
    @3
    @31
    @33
    simprl
    @31
    @23
    @37
    @9
    cS
    @21
    elinti
    imp
    #
    sylan
    @35
    @33
    @23
    @38
    @3
    @31
    @33
    simprr
    @33
    @23
    @38
    @10
    cS
    @21
    elinti
    imp
    sylan
    @11
    @21
    cG
    @9
    @10
    @11
    eqid
    #
    subgcl
    syl3anc
    ralrimiva
    vg
    @12
    cS
    @9
    @10
    @11
    ovex
    elint2
    sylibr
    anassrs
    ralrimiva
    @32
    @16
    @21
    wcel
    #
    vg
    cS
    wral
    @17
    @32
    @41
    vg
    cS
    @32
    @23
    wa
    @25
    @37
    @41
    @3
    @23
    @25
    @31
    @26
    adantlr
    @31
    @23
    @37
    @3
    @39
    adantll
    @21
    cG
    @15
    @9
    @15
    eqid
    #
    subginvcl
    syl2anc
    ralrimiva
    vg
    @16
    cS
    @9
    @15
    fvex
    elint2
    sylibr
    jca
    ralrimiva
    @3
    @0
    c0
    wne
    #
    cG
    cgrp
    wcel
    #
    @5
    @7
    @8
    @19
    w3a
    wb
    cS
    @0
    ssn0
    @43
    @25
    vg
    wex
    @44
    vg
    @0
    n0
    @25
    @44
    vg
    @21
    cG
    subgrcl
    exlimiv
    sylbi
    vx
    vy
    @6
    @11
    @4
    cG
    @15
    @27
    @40
    @42
    issubg2
    3syl
    mpbir3and
end
