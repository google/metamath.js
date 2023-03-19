include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "ccnfld.mm"
include "cinvr.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cc.mm"
include "wceq.mm"
include "csubrg.mm"
include "wss.mm"
include "cress.mm"
include "cin.mm"
include "cphsubrglem.mm"
include "simp3d.mm"
include "3ad2ant1.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "cnfldinv.mm"
include "syl2anc.mm"
include "cui.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "eqid.mm"
include "cnfld0.mm"
include "subrg0.mm"
include "simp1d.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "neeqtrd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cdr.mm"
include "crg.mm"
include "isdrng.mm"
include "simprbi.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "wb.mm"
include "subrgunit.mm"
include "mpbid.mm"
include "eqeltrrd.mm"

theorem cphreccllem
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cK: class K
  let cX: class X
  assume cphsubrglem.k: |- K = ( Base ` F )
  assume cphsubrglem.1: |- ( ph -> F = ( CCfld |`s A ) )
  assume cphsubrglem.2: |- ( ph -> F e. DivRing )


  assert |- ( ( ph /\ X e. K /\ X =/= 0 ) -> ( 1 / X ) e. K )

  proof
    wph
    cX
    cK
    wcel
    #
    cX
    cc0
    wne
    #
    w3a
    #
    cX
    ccnfld
    cinvr
    cfv
    #
    cfv
    #
    c1
    cX
    cdiv
    co
    #
    cK
    @2
    cX
    cc
    wcel
    @1
    @4
    @5
    wceq
    @2
    cK
    cc
    cX
    @2
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    cK
    cc
    wss
    wph
    @0
    @6
    @1
    wph
    cF
    ccnfld
    cK
    cress
    co
    #
    wceq
    #
    cK
    cA
    cc
    cin
    wceq
    #
    @6
    wph
    cA
    cF
    cK
    cphsubrglem.k
    cphsubrglem.1
    cphsubrglem.2
    cphsubrglem
    #
    simp3d
    3ad2ant1
    #
    cK
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    wph
    @0
    @1
    simp2
    #
    sseldd
    wph
    @0
    @1
    simp3
    #
    cX
    cnfldinv
    syl2anc
    @2
    cX
    ccnfld
    cui
    cfv
    #
    wcel
    #
    @0
    @4
    cK
    wcel
    #
    @2
    cX
    @7
    cui
    cfv
    #
    wcel
    #
    @15
    @0
    @16
    w3a
    #
    @2
    cX
    cK
    cF
    c0g
    cfv
    #
    csn
    cdif
    #
    @17
    @2
    @0
    cX
    @20
    wne
    cX
    @21
    wcel
    @12
    @2
    cX
    cc0
    @20
    @13
    @2
    cc0
    @7
    c0g
    cfv
    #
    @20
    @2
    @6
    cc0
    @22
    wceq
    @11
    cK
    ccnfld
    @7
    cc0
    @7
    eqid
    #
    cnfld0
    subrg0
    syl
    @2
    cF
    @7
    c0g
    wph
    @0
    @8
    @1
    wph
    @8
    @9
    @6
    @10
    simp1d
    3ad2ant1
    #
    fveq2d
    eqtr4d
    neeqtrd
    cX
    cK
    @20
    eldifsn
    sylanbrc
    @2
    cF
    cui
    cfv
    #
    @21
    @17
    @2
    cF
    cdr
    wcel
    #
    @25
    @21
    wceq
    #
    wph
    @0
    @26
    @1
    cphsubrglem.2
    3ad2ant1
    @26
    cF
    crg
    wcel
    @27
    cK
    cF
    @25
    @20
    cphsubrglem.k
    @25
    eqid
    @20
    eqid
    isdrng
    simprbi
    syl
    @2
    cF
    @7
    cui
    @24
    fveq2d
    eqtr3d
    eleqtrd
    @2
    @6
    @18
    @19
    wb
    @11
    cK
    ccnfld
    @7
    @14
    @3
    @17
    cX
    @23
    @14
    eqid
    @17
    eqid
    @3
    eqid
    subrgunit
    syl
    mpbid
    simp3d
    eqeltrrd
end
