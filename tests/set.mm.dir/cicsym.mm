include "ccat.mm"
include "wcel.mm"
include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cbs.mm"
include "cicrcl.mm"
include "ciclcl.mm"
include "cv.mm"
include "ciso.mm"
include "co.mm"
include "wex.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "adantl.mm"
include "cic.mm"
include "wi.mm"
include "cinv.mm"
include "crn.mm"
include "cdm.mm"
include "isoval.mm"
include "ccnv.mm"
include "invsym2.mm"
include "eqcomd.mm"
include "dmeqd.mm"
include "df-rn.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrng.mm"
include "mp1i.mm"
include "bitrd.mm"
include "cop.mm"
include "df-br.mm"
include "exbii.mm"
include "opeldm.mm"
include "adantr.mm"
include "brcici.mm"
include "ex.mm"
include "sylbid.mm"
include "com12.mm"
include "syl.mm"
include "exlimiv.mm"
include "syl5bi.mm"
include "impancom.mm"
include "mp2and.mm"

theorem cicsym
  let cC: class C
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g


  assert |- ( ( C e. Cat /\ R ( ~=c ` C ) S ) -> S ( ~=c ` C ) R )

  proof
    cC
    ccat
    wcel
    #
    cR
    cS
    cC
    ccic
    cfv
    #
    wbr
    #
    wa
    cS
    cC
    cbs
    cfv
    #
    wcel
    #
    cR
    @3
    wcel
    #
    cS
    cR
    @1
    wbr
    #
    cC
    cR
    cS
    cicrcl
    cC
    cR
    cS
    ciclcl
    @0
    @4
    @5
    wa
    #
    @2
    @6
    @0
    @7
    wa
    #
    @2
    vf
    cv
    #
    cR
    cS
    cC
    ciso
    cfv
    #
    co
    #
    wcel
    #
    vf
    wex
    #
    @6
    @8
    @3
    cC
    vf
    @10
    cR
    cS
    @10
    eqid
    #
    @3
    eqid
    #
    @0
    @7
    simpl
    #
    @7
    @5
    @0
    @4
    @5
    simpr
    adantl
    #
    @7
    @4
    @0
    @4
    @5
    simpl
    adantl
    #
    cic
    @13
    @8
    @6
    @12
    @8
    @6
    wi
    #
    vf
    @8
    @12
    @6
    @8
    @12
    vg
    cv
    #
    @9
    cS
    cR
    cC
    cinv
    cfv
    #
    co
    #
    wbr
    #
    vg
    wex
    #
    @6
    @8
    @12
    @9
    @22
    crn
    #
    wcel
    #
    @24
    @8
    @11
    @25
    @9
    @8
    @11
    cR
    cS
    @21
    co
    #
    cdm
    #
    @25
    @8
    @3
    cC
    @10
    @21
    cR
    cS
    @15
    @21
    eqid
    #
    @16
    @17
    @18
    @14
    isoval
    @8
    @28
    @22
    ccnv
    #
    cdm
    @25
    @8
    @27
    @30
    @8
    @30
    @27
    @8
    @3
    cC
    @21
    cS
    cR
    @15
    @29
    @16
    @18
    @17
    invsym2
    eqcomd
    dmeqd
    @22
    df-rn
    syl6eqr
    eqtrd
    eleq2d
    @9
    cvv
    wcel
    @26
    @24
    wb
    @8
    vf
    vex
    #
    vg
    @9
    @22
    cvv
    elrng
    mp1i
    bitrd
    @24
    @20
    @9
    cop
    @22
    wcel
    #
    vg
    wex
    #
    @8
    @6
    @23
    @32
    vg
    @20
    @9
    @22
    df-br
    exbii
    @33
    @8
    @6
    @32
    @19
    vg
    @32
    @20
    @22
    cdm
    #
    wcel
    #
    @19
    @20
    @9
    @22
    vg
    vex
    @31
    opeldm
    @8
    @35
    @6
    @8
    @35
    @20
    cS
    cR
    @10
    co
    #
    wcel
    #
    @6
    @8
    @34
    @36
    @20
    @8
    @36
    @34
    @8
    @3
    cC
    @10
    @21
    cS
    cR
    @15
    @29
    @16
    @18
    @17
    @14
    isoval
    eqcomd
    eleq2d
    @8
    @37
    @6
    @8
    @37
    wa
    @3
    cC
    @20
    @10
    cS
    cR
    @14
    @15
    @8
    @0
    @37
    @16
    adantr
    @8
    @4
    @37
    @18
    adantr
    @8
    @5
    @37
    @17
    adantr
    @8
    @37
    simpr
    brcici
    ex
    sylbid
    com12
    syl
    exlimiv
    com12
    syl5bi
    sylbid
    com12
    exlimiv
    com12
    sylbid
    impancom
    mp2and
end
