include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "c0.mm"
include "eqidd.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "cword.mm"
include "wa.mm"
include "cconcat.mm"
include "eqid.mm"
include "frmdadd.mm"
include "frmdelbas.mm"
include "ccatcl.mm"
include "syl2an.mm"
include "eqeltrd.mm"
include "3adant1.mm"
include "wceq.mm"
include "frmdbas.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "simpr1.mm"
include "syl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "ccatass.mm"
include "syl3anc.mm"
include "syl2anc.mm"
include "adantr.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "wrd0.mm"
include "syl5eleqr.mm"
include "sylan.mm"
include "adantl.mm"
include "ccatlid.mm"
include "eqtrd.mm"
include "ancoms.mm"
include "ccatrid.mm"
include "ismndd.mm"

theorem frmdmnd
  let cI: class I
  let cM: class M
  let cV: class V
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cU: class U
  let cW: class W
  assume frmdmnd.m: |- M = ( freeMnd ` I )


  assert |- ( I e. V -> M e. Mnd )

  proof
    cI
    cV
    wcel
    #
    vx
    vy
    vz
    cM
    cbs
    cfv
    #
    cM
    cplusg
    cfv
    #
    cM
    c0
    @0
    @1
    eqidd
    @0
    @2
    eqidd
    @0
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    w3a
    @3
    @5
    @2
    co
    #
    cI
    cword
    #
    @1
    @4
    @6
    @7
    @8
    wcel
    @0
    @4
    @6
    wa
    @7
    @3
    @5
    cconcat
    co
    #
    @8
    @1
    @2
    cI
    cM
    @3
    @5
    frmdmnd.m
    @1
    eqid
    #
    @2
    eqid
    #
    frmdadd
    #
    @4
    @3
    @8
    wcel
    #
    @5
    @8
    wcel
    #
    @9
    @8
    wcel
    #
    @6
    @1
    cI
    cM
    @3
    frmdmnd.m
    @10
    frmdelbas
    #
    @1
    cI
    cM
    @5
    frmdmnd.m
    @10
    frmdelbas
    #
    cI
    @3
    @5
    ccatcl
    syl2an
    #
    eqeltrd
    3adant1
    @0
    @4
    @1
    @8
    wceq
    #
    @6
    @1
    cI
    cM
    cV
    frmdmnd.m
    @10
    frmdbas
    #
    3ad2ant1
    eleqtrrd
    @0
    @4
    @6
    vz
    cv
    #
    @1
    wcel
    #
    w3a
    #
    wa
    #
    @9
    @21
    @2
    co
    #
    @3
    @5
    @21
    cconcat
    co
    #
    @2
    co
    #
    @7
    @21
    @2
    co
    @3
    @5
    @21
    @2
    co
    #
    @2
    co
    @24
    @9
    @21
    cconcat
    co
    #
    @3
    @26
    cconcat
    co
    #
    @25
    @27
    @24
    @13
    @14
    @21
    @8
    wcel
    #
    @29
    @30
    wceq
    @24
    @4
    @13
    @0
    @4
    @6
    @22
    simpr1
    #
    @16
    syl
    @24
    @6
    @14
    @0
    @4
    @6
    @22
    simpr2
    #
    @17
    syl
    #
    @24
    @22
    @31
    @0
    @4
    @6
    @22
    simpr3
    #
    @1
    cI
    cM
    @21
    frmdmnd.m
    @10
    frmdelbas
    syl
    #
    cI
    @3
    @5
    @21
    ccatass
    syl3anc
    @24
    @9
    @1
    wcel
    @22
    @25
    @29
    wceq
    @24
    @9
    @8
    @1
    @24
    @4
    @6
    @15
    @32
    @33
    @18
    syl2anc
    @0
    @19
    @23
    @20
    adantr
    #
    eleqtrrd
    @35
    @1
    @2
    cI
    cM
    @9
    @21
    frmdmnd.m
    @10
    @11
    frmdadd
    syl2anc
    @24
    @4
    @26
    @1
    wcel
    @27
    @30
    wceq
    @32
    @24
    @26
    @8
    @1
    @24
    @14
    @31
    @26
    @8
    wcel
    @34
    @36
    cI
    @5
    @21
    ccatcl
    syl2anc
    @37
    eleqtrrd
    @1
    @2
    cI
    cM
    @3
    @26
    frmdmnd.m
    @10
    @11
    frmdadd
    syl2anc
    3eqtr4d
    @24
    @7
    @9
    @21
    @2
    @24
    @4
    @6
    @7
    @9
    wceq
    @32
    @33
    @12
    syl2anc
    oveq1d
    @24
    @28
    @26
    @3
    @2
    @24
    @6
    @22
    @28
    @26
    wceq
    @33
    @35
    @1
    @2
    cI
    cM
    @5
    @21
    frmdmnd.m
    @10
    @11
    frmdadd
    syl2anc
    oveq2d
    3eqtr4d
    @0
    c0
    @8
    @1
    cI
    wrd0
    @20
    syl5eleqr
    #
    @0
    @4
    wa
    #
    c0
    @3
    @2
    co
    #
    c0
    @3
    cconcat
    co
    #
    @3
    @0
    c0
    @1
    wcel
    #
    @4
    @40
    @41
    wceq
    @38
    @1
    @2
    cI
    cM
    c0
    @3
    frmdmnd.m
    @10
    @11
    frmdadd
    sylan
    @39
    @13
    @41
    @3
    wceq
    @4
    @13
    @0
    @16
    adantl
    #
    cI
    @3
    ccatlid
    syl
    eqtrd
    @39
    @3
    c0
    @2
    co
    #
    @3
    c0
    cconcat
    co
    #
    @3
    @0
    @42
    @4
    @44
    @45
    wceq
    #
    @38
    @4
    @42
    @46
    @1
    @2
    cI
    cM
    @3
    c0
    frmdmnd.m
    @10
    @11
    frmdadd
    ancoms
    sylan
    @39
    @13
    @45
    @3
    wceq
    @43
    cI
    @3
    ccatrid
    syl
    eqtrd
    ismndd
end
