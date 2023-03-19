include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cvma.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "cuni.mm"
include "clog.mm"
include "cc0.mm"
include "cif.mm"
include "cn0.mm"
include "prmnn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "syl2an.mm"
include "eqid.mm"
include "vmaval.mm"
include "syl.mm"
include "csn.mm"
include "cab.mm"
include "df-rab.mm"
include "wi.mm"
include "w3a.mm"
include "prmdvdsexpb.mm"
include "biimpd.mm"
include "3coml.mm"
include "3expa.mm"
include "expimpd.mm"
include "simpl.mm"
include "cz.mm"
include "prmz.mm"
include "iddvdsexp.mm"
include "sylan.mm"
include "jca.mm"
include "eleq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "velsn.mm"
include "syl6bbr.mm"
include "abbi1dv.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "hashsng.mm"
include "adantr.mm"
include "eqtrd.mm"
include "iftrued.mm"
include "unieqd.mm"
include "unisng.mm"
include "3eqtrd.mm"

theorem vmappw
  let cP: class P
  let cK: class K
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B


  assert |- ( ( P e. Prime /\ K e. NN ) -> ( Lam ` ( P ^ K ) ) = ( log ` P ) )

  proof
    cP
    cprime
    wcel
    #
    cK
    cn
    wcel
    #
    wa
    #
    cP
    cK
    cexp
    co
    #
    cvma
    cfv
    #
    vp
    cv
    #
    @3
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    c1
    wceq
    #
    @7
    cuni
    #
    clog
    cfv
    #
    cc0
    cif
    #
    @11
    cP
    clog
    cfv
    @2
    @3
    cn
    wcel
    #
    @4
    @12
    wceq
    @0
    cP
    cn
    wcel
    cK
    cn0
    wcel
    @13
    @1
    cP
    prmnn
    cK
    nnnn0
    cP
    cK
    nnexpcl
    syl2an
    @3
    @7
    vp
    @7
    eqid
    vmaval
    syl
    @2
    @9
    @11
    cc0
    @2
    @8
    cP
    csn
    #
    chash
    cfv
    #
    c1
    @2
    @7
    @14
    chash
    @2
    @7
    @5
    cprime
    wcel
    #
    @6
    wa
    #
    vp
    cab
    @14
    @6
    vp
    cprime
    df-rab
    @2
    @17
    vp
    @14
    @2
    @17
    @5
    cP
    wceq
    #
    @5
    @14
    wcel
    @2
    @17
    @18
    @2
    @16
    @6
    @18
    @0
    @1
    @16
    @6
    @18
    wi
    #
    @16
    @0
    @1
    @19
    @16
    @0
    @1
    w3a
    @6
    @18
    @5
    cP
    cK
    prmdvdsexpb
    biimpd
    3coml
    3expa
    expimpd
    @2
    @17
    @18
    @0
    cP
    @3
    cdvds
    wbr
    #
    wa
    @2
    @0
    @20
    @0
    @1
    simpl
    @0
    cP
    cz
    wcel
    @1
    @20
    cP
    prmz
    cP
    cK
    iddvdsexp
    sylan
    jca
    @18
    @16
    @0
    @6
    @20
    @5
    cP
    cprime
    eleq1
    @5
    cP
    @3
    cdvds
    breq1
    anbi12d
    syl5ibrcom
    impbid
    vp
    cP
    velsn
    syl6bbr
    abbi1dv
    syl5eq
    #
    fveq2d
    @0
    @15
    c1
    wceq
    @1
    cP
    cprime
    hashsng
    adantr
    eqtrd
    iftrued
    @2
    @10
    cP
    clog
    @2
    @10
    @14
    cuni
    #
    cP
    @2
    @7
    @14
    @21
    unieqd
    @0
    @22
    cP
    wceq
    @1
    cP
    cprime
    unisng
    adantr
    eqtrd
    fveq2d
    3eqtrd
end
