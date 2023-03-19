include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "cin.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "fveq2d.mm"
include "cvv.mm"
include "crg.mm"
include "c0g.mm"
include "wa.mm"
include "cdr.mm"
include "drngring.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "eqid.mm"
include "ring0cl.mm"
include "reldmress.mm"
include "elbasov.mm"
include "3syl.mm"
include "simprd.mm"
include "cnfldbas.mm"
include "ressbas.mm"
include "eqtr4d.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "ressinbas.mm"
include "wss.mm"
include "c1.mm"
include "cnring.mm"
include "jctil.mm"
include "ressbasss.mm"
include "syl6eqss.mm"
include "syl5eqss.mm"
include "cur.mm"
include "cc0.mm"
include "wn.mm"
include "wne.mm"
include "drngunz.mm"
include "csubg.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "mp1i.mm"
include "issubg.mm"
include "syl3anbrc.mm"
include "cnfld0.mm"
include "subg0.mm"
include "neeqtrd.mm"
include "neneqd.mm"
include "c2.mm"
include "cexp.mm"
include "wo.mm"
include "cmul.mm"
include "ringidcl.mm"
include "sseldd.mm"
include "sqvald.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "cmulr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "ax-mp.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "wb.mm"
include "sq01.mm"
include "mpbid.mm"
include "ord.mm"
include "mpd.mm"
include "jca.mm"
include "cnfld1.mm"
include "issubrg.mm"
include "sylanbrc.mm"
include "3jca.mm"

theorem cphsubrglem
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cK: class K
  assume cphsubrglem.k: |- K = ( Base ` F )
  assume cphsubrglem.1: |- ( ph -> F = ( CCfld |`s A ) )
  assume cphsubrglem.2: |- ( ph -> F e. DivRing )


  assert |- ( ph -> ( F = ( CCfld |`s K ) /\ K = ( A i^i CC ) /\ K e. ( SubRing ` CCfld ) ) )

  proof
    wph
    cF
    ccnfld
    cK
    cress
    co
    #
    wceq
    cK
    cA
    cc
    cin
    #
    wceq
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    wph
    cF
    ccnfld
    cA
    cress
    co
    #
    @0
    cphsubrglem.1
    wph
    @0
    ccnfld
    @1
    cress
    co
    #
    @3
    wph
    cK
    @1
    ccnfld
    cress
    wph
    cK
    cF
    cbs
    cfv
    #
    @1
    cphsubrglem.k
    wph
    @5
    @3
    cbs
    cfv
    #
    @1
    wph
    cF
    @3
    cbs
    cphsubrglem.1
    fveq2d
    #
    wph
    cA
    cvv
    wcel
    #
    @1
    @6
    wceq
    wph
    ccnfld
    cvv
    wcel
    #
    @8
    wph
    @3
    crg
    wcel
    @3
    c0g
    cfv
    #
    @6
    wcel
    @9
    @8
    wa
    wph
    cF
    @3
    crg
    cphsubrglem.1
    wph
    cF
    cdr
    wcel
    #
    cF
    crg
    wcel
    #
    cphsubrglem.2
    cF
    drngring
    syl
    #
    eqeltrrd
    @6
    @3
    @10
    @6
    eqid
    #
    @10
    eqid
    ring0cl
    @10
    @6
    @3
    cress
    ccnfld
    cA
    reldmress
    @3
    eqid
    #
    @14
    elbasov
    3syl
    simprd
    #
    cA
    cc
    @3
    cvv
    ccnfld
    @15
    cnfldbas
    ressbas
    syl
    eqtr4d
    syl5eq
    #
    oveq2d
    wph
    @8
    @3
    @4
    wceq
    @16
    cA
    cc
    ccnfld
    cvv
    cnfldbas
    ressinbas
    syl
    eqtr4d
    eqtr4d
    #
    @17
    wph
    ccnfld
    crg
    wcel
    #
    @0
    crg
    wcel
    #
    wa
    cK
    cc
    wss
    #
    c1
    cK
    wcel
    #
    wa
    @2
    wph
    @20
    @19
    wph
    cF
    @0
    crg
    @18
    @13
    eqeltrrd
    #
    cnring
    jctil
    wph
    @21
    @22
    wph
    cK
    @5
    cc
    cphsubrglem.k
    wph
    @5
    @6
    cc
    @7
    cA
    cc
    @3
    ccnfld
    @15
    cnfldbas
    ressbasss
    syl6eqss
    syl5eqss
    #
    wph
    cF
    cur
    cfv
    #
    c1
    cK
    wph
    @25
    cc0
    wceq
    #
    wn
    @25
    c1
    wceq
    #
    wph
    @25
    cc0
    wph
    @25
    cF
    c0g
    cfv
    #
    cc0
    wph
    @11
    @25
    @28
    wne
    cphsubrglem.2
    cF
    @25
    @28
    @28
    eqid
    @25
    eqid
    #
    drngunz
    syl
    wph
    @28
    @0
    c0g
    cfv
    #
    cc0
    wph
    cF
    @0
    c0g
    @18
    fveq2d
    wph
    cK
    ccnfld
    csubg
    cfv
    wcel
    #
    cc0
    @30
    wceq
    wph
    ccnfld
    cgrp
    wcel
    #
    @21
    @0
    cgrp
    wcel
    #
    @31
    @19
    @32
    wph
    cnring
    ccnfld
    ringgrp
    mp1i
    @24
    wph
    @20
    @33
    @23
    @0
    ringgrp
    syl
    cc
    cK
    ccnfld
    cnfldbas
    issubg
    syl3anbrc
    cK
    ccnfld
    @0
    cc0
    @0
    eqid
    #
    cnfld0
    subg0
    syl
    eqtr4d
    neeqtrd
    neneqd
    wph
    @26
    @27
    wph
    @25
    c2
    cexp
    co
    #
    @25
    wceq
    #
    @26
    @27
    wo
    #
    wph
    @35
    @25
    @25
    cmul
    co
    @0
    cur
    cfv
    #
    @25
    cmul
    co
    #
    @25
    wph
    @25
    wph
    cK
    cc
    @25
    @24
    wph
    @12
    @25
    cK
    wcel
    @13
    cK
    cF
    @25
    cphsubrglem.k
    @29
    ringidcl
    syl
    #
    sseldd
    #
    sqvald
    wph
    @25
    @38
    @25
    cmul
    wph
    cF
    @0
    cur
    @18
    fveq2d
    oveq1d
    wph
    @20
    @25
    @0
    cbs
    cfv
    #
    wcel
    @39
    @25
    wceq
    @23
    wph
    @25
    cK
    @42
    @40
    wph
    cK
    @5
    @42
    cphsubrglem.k
    wph
    cF
    @0
    cbs
    @18
    fveq2d
    syl5eq
    eleqtrd
    @42
    @0
    cmul
    @38
    @25
    @42
    eqid
    cK
    cvv
    wcel
    cmul
    @0
    cmulr
    cfv
    wceq
    cK
    @5
    cvv
    cphsubrglem.k
    cF
    cbs
    fvex
    eqeltri
    cK
    ccnfld
    @0
    cmul
    cvv
    @34
    cnfldmul
    ressmulr
    ax-mp
    @38
    eqid
    ringlidm
    syl2anc
    3eqtrd
    wph
    @25
    cc
    wcel
    @36
    @37
    wb
    @41
    @25
    sq01
    syl
    mpbid
    ord
    mpd
    @40
    eqeltrrd
    jca
    cK
    cc
    ccnfld
    c1
    cnfldbas
    cnfld1
    issubrg
    sylanbrc
    3jca
end
