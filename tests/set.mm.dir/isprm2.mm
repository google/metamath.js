include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "cn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cpr.mm"
include "wss.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "1nprm.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "mtoi.mm"
include "neqned.mm"
include "pm4.71i.mm"
include "c2o.mm"
include "cen.mm"
include "isprm.mm"
include "wb.mm"
include "isprm2lem.mm"
include "eqss.mm"
include "imbi2i.mm"
include "1idssfct.mm"
include "jcab.mm"
include "mpbiran2.mm"
include "bitri.mm"
include "pm5.74ri.mm"
include "adantr.mm"
include "bitrd.mm"
include "expcom.mm"
include "pm5.32d.mm"
include "syl5bb.mm"
include "pm5.32ri.mm"
include "ancom.mm"
include "anass.mm"
include "bitr4i.mm"
include "eluz2b3.mm"
include "anbi1i.mm"
include "wal.mm"
include "dfss2.mm"
include "breq1.mm"
include "elrab.mm"
include "vex.mm"
include "elpr.mm"
include "imbi12i.mm"
include "impexp.mm"
include "albii.mm"
include "df-ral.mm"
include "anbi2i.mm"
include "3bitri.mm"

theorem isprm2
  let vz: setvar z
  let cP: class P
  let vn: setvar n

  disjoint P z
  disjoint n z
  disjoint P n
  assert |- ( P e. Prime <-> ( P e. ( ZZ>= ` 2 ) /\ A. z e. NN ( z || P -> ( z = 1 \/ z = P ) ) ) )

  proof
    cP
    cprime
    wcel
    #
    @0
    cP
    c1
    wne
    #
    wa
    cP
    cn
    wcel
    #
    vn
    cv
    #
    cP
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    c1
    cP
    cpr
    #
    wss
    #
    wa
    #
    @1
    wa
    #
    cP
    c2
    cuz
    cfv
    wcel
    #
    vz
    cv
    #
    cP
    cdvds
    wbr
    #
    @11
    c1
    wceq
    @11
    cP
    wceq
    wo
    #
    wi
    #
    vz
    cn
    wral
    #
    wa
    #
    @0
    @1
    @0
    cP
    c1
    @0
    cP
    c1
    wceq
    #
    c1
    cprime
    wcel
    #
    1nprm
    @17
    @0
    @18
    cP
    c1
    cprime
    eleq1
    biimpcd
    mtoi
    neqned
    pm4.71i
    @1
    @0
    @8
    @0
    @2
    @5
    c2o
    cen
    wbr
    #
    wa
    @1
    @8
    cP
    vn
    isprm
    @1
    @2
    @19
    @7
    @2
    @1
    @19
    @7
    wb
    @2
    @1
    wa
    #
    @19
    @5
    @6
    wceq
    #
    @7
    cP
    vn
    isprm2lem
    @2
    @21
    @7
    wb
    @1
    @2
    @21
    @7
    @2
    @21
    wi
    @2
    @7
    @6
    @5
    wss
    #
    wa
    #
    wi
    #
    @2
    @7
    wi
    #
    @21
    @23
    @2
    @5
    @6
    eqss
    imbi2i
    @24
    @25
    @2
    @22
    wi
    vn
    cP
    1idssfct
    @2
    @7
    @22
    jcab
    mpbiran2
    bitri
    pm5.74ri
    adantr
    bitrd
    expcom
    pm5.32d
    syl5bb
    pm5.32ri
    @9
    @1
    @2
    wa
    #
    @7
    wa
    #
    @10
    @7
    wa
    @16
    @9
    @1
    @8
    wa
    @27
    @8
    @1
    ancom
    @1
    @2
    @7
    anass
    bitr4i
    @26
    @10
    @7
    @26
    @20
    @10
    @1
    @2
    ancom
    cP
    eluz2b3
    bitr4i
    anbi1i
    @7
    @15
    @10
    @7
    @11
    @5
    wcel
    #
    @11
    @6
    wcel
    #
    wi
    #
    vz
    wal
    #
    @15
    vz
    @5
    @6
    dfss2
    @31
    @11
    cn
    wcel
    #
    @14
    wi
    #
    vz
    wal
    @15
    @30
    @33
    vz
    @30
    @32
    @12
    wa
    #
    @13
    wi
    @33
    @28
    @34
    @29
    @13
    @4
    @12
    vn
    @11
    cn
    @3
    @11
    cP
    cdvds
    breq1
    elrab
    @11
    c1
    cP
    vz
    vex
    elpr
    imbi12i
    @32
    @12
    @13
    impexp
    bitri
    albii
    @14
    vz
    cn
    df-ral
    bitr4i
    bitri
    anbi2i
    3bitri
    3bitri
end
