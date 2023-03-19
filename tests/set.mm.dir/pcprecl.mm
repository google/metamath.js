include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "cv.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "pclem.mm"
include "suprzcl2.mm"
include "syl.mm"
include "syl5eqel.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "crab.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "sylib.mm"

theorem pcprecl
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
  assert |- ( ( P e. ( ZZ>= ` 2 ) /\ ( N e. ZZ /\ N =/= 0 ) ) -> ( S e. NN0 /\ ( P ^ S ) || N ) )

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
    cS
    cA
    wcel
    cS
    cn0
    wcel
    cP
    cS
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    wa
    @0
    cS
    cA
    cr
    clt
    csup
    #
    cA
    pclem.2
    @0
    cA
    cz
    wss
    cA
    c0
    wne
    vz
    cv
    vy
    cv
    cle
    wbr
    vz
    cA
    wral
    vy
    cz
    wrex
    w3a
    @3
    cA
    wcel
    vy
    vz
    cA
    cP
    vn
    cN
    pclem.1
    pclem
    vy
    vz
    cA
    suprzcl2
    syl
    syl5eqel
    cP
    vx
    cv
    #
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @2
    vx
    cS
    cn0
    cA
    @4
    cS
    wceq
    @5
    @1
    cN
    cdvds
    @4
    cS
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
    @6
    vx
    cn0
    crab
    pclem.1
    @9
    @6
    vn
    vx
    cn0
    @7
    @4
    wceq
    @8
    @5
    cN
    cdvds
    @7
    @4
    cP
    cexp
    oveq2
    breq1d
    cbvrabv
    eqtri
    elrab2
    sylib
end
