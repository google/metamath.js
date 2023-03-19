include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cle.mm"
include "cn0.mm"
include "cr.mm"
include "wn.mm"
include "pcprecl.mm"
include "simpld.mm"
include "nn0re.mm"
include "clt.mm"
include "ltp1.mm"
include "wb.mm"
include "peano2re.mm"
include "ltnle.mm"
include "mpdan.mm"
include "mpbid.mm"
include "3syl.mm"
include "wss.mm"
include "c0.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "pclem.mm"
include "wi.mm"
include "peano2nn0.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "crab.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "simplbi2.mm"
include "csup.mm"
include "suprzub.mm"
include "syl6breqr.mm"
include "3expia.mm"
include "3adant2.mm"
include "sylsyld.mm"
include "mtod.mm"

theorem pcprendvds
  let cA: class A
  let cP: class P
  let cS: class S
  let vn: setvar n
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pclem.1: |- A = { n e. NN0 | ( P ^ n ) || N }
  assume pclem.2: |- S = sup ( A , RR , < )

  disjoint N n
  disjoint P n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S x
  assert |- ( ( P e. ( ZZ>= ` 2 ) /\ ( N e. ZZ /\ N =/= 0 ) ) -> -. ( P ^ ( S + 1 ) ) || N )

  proof
    cP
    c2
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    cN
    cc0
    wne
    wa
    wa
    #
    cP
    cS
    c1
    caddc
    co
    #
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @1
    cS
    cle
    wbr
    #
    @0
    cS
    cn0
    wcel
    #
    cS
    cr
    wcel
    #
    @4
    wn
    #
    @0
    @5
    cP
    cS
    cexp
    co
    cN
    cdvds
    wbr
    cA
    cP
    cS
    vn
    cN
    pclem.1
    pclem.2
    pcprecl
    simpld
    #
    cS
    nn0re
    @6
    cS
    @1
    clt
    wbr
    #
    @7
    cS
    ltp1
    @6
    @1
    cr
    wcel
    @9
    @7
    wb
    cS
    peano2re
    cS
    @1
    ltnle
    mpdan
    mpbid
    3syl
    @0
    cA
    cz
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cz
    wrex
    #
    w3a
    @3
    @1
    cA
    wcel
    #
    @4
    vx
    vy
    cA
    cP
    vn
    cN
    pclem.1
    pclem
    @0
    @5
    @1
    cn0
    wcel
    #
    @3
    @14
    wi
    @8
    cS
    peano2nn0
    @14
    @15
    @3
    cP
    @12
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @3
    vx
    @1
    cn0
    cA
    @12
    @1
    wceq
    @16
    @2
    cN
    cdvds
    @12
    @1
    cP
    cexp
    oveq2
    breq1d
    cA
    cP
    vn
    cv
    #
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    vn
    cn0
    crab
    @17
    vx
    cn0
    crab
    pclem.1
    @20
    @17
    vn
    vx
    cn0
    @18
    @12
    wceq
    @19
    @16
    cN
    cdvds
    @18
    @12
    cP
    cexp
    oveq2
    breq1d
    cbvrabv
    eqtri
    elrab2
    simplbi2
    3syl
    @10
    @13
    @14
    @4
    wi
    @11
    @10
    @13
    @14
    @4
    @10
    @13
    @14
    w3a
    @1
    cA
    cr
    clt
    csup
    cS
    cle
    vx
    vy
    cA
    @1
    suprzub
    pclem.2
    syl6breqr
    3expia
    3adant2
    sylsyld
    mtod
end
