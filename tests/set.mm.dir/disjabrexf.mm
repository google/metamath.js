include "wdisj.mm"
include "cv.mm"
include "wcel.mm"
include "csb.mm"
include "wa.mm"
include "cab.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "nfdisj1.mm"
include "nfcv.mm"
include "nfcri.mm"
include "nfcsb1v.mm"
include "nfan.mm"
include "nfab.mm"
include "nfuni.mm"
include "nfcsb1.mm"
include "nfeq1.mm"
include "nfral.mm"
include "eqeq2.mm"
include "raleqbi1dv.mm"
include "vex.mm"
include "a1i.mm"
include "csn.mm"
include "simplll.mm"
include "simpllr.mm"
include "simprl.mm"
include "simplr.mm"
include "simprr.mm"
include "csbeq1a.mm"
include "disjif2.mm"
include "syl122anc.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "eleq2d.mm"
include "syl.mm"
include "mpbid.mm"
include "jca.mm"
include "impbida.mm"
include "equcom.mm"
include "syl6bb.mm"
include "abbidv.mm"
include "df-sn.mm"
include "syl6eqr.mm"
include "unieqd.mm"
include "unisn.mm"
include "syl6eq.mm"
include "csbeq1.mm"
include "csbid.mm"
include "ralrimiva.mm"
include "elabreximd.mm"
include "invdisj.mm"

theorem disjabrexf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  assume disjabrexf.1: |- F/_ x A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  assert |- ( Disj_ x e. A B -> Disj_ y e. { z | E. x e. A z = B } y )

  proof
    vx
    cA
    cB
    wdisj
    #
    vx
    vi
    cv
    #
    cA
    wcel
    #
    vj
    cv
    #
    vx
    @1
    cB
    csb
    #
    wcel
    #
    wa
    #
    vi
    cab
    #
    cuni
    #
    cB
    csb
    #
    vy
    cv
    #
    wceq
    #
    vj
    @10
    wral
    #
    vy
    vz
    cv
    cB
    wceq
    vx
    cA
    wrex
    vz
    cab
    #
    wral
    vy
    @13
    @10
    wdisj
    @0
    @12
    vy
    @13
    @0
    @9
    cB
    wceq
    #
    vj
    cB
    wral
    @12
    vx
    vz
    @10
    cB
    cA
    cvv
    vx
    cA
    cB
    nfdisj1
    @11
    vx
    vj
    @10
    vx
    @10
    nfcv
    vx
    @9
    @10
    vx
    @8
    cB
    vx
    @7
    @6
    vx
    vi
    @2
    @5
    vx
    vx
    vi
    cA
    disjabrexf.1
    nfcri
    vx
    vj
    @4
    vx
    @1
    cB
    nfcsb1v
    #
    nfcri
    nfan
    nfab
    nfuni
    nfcsb1
    nfeq1
    nfral
    @11
    @14
    vj
    @10
    cB
    @10
    cB
    @9
    eqeq2
    raleqbi1dv
    @10
    cvv
    wcel
    @0
    vy
    vex
    a1i
    @0
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @14
    vj
    cB
    @18
    @3
    cB
    wcel
    #
    wa
    #
    @8
    @16
    wceq
    #
    @14
    @20
    @8
    @16
    csn
    #
    cuni
    @16
    @20
    @7
    @22
    @20
    @7
    @1
    @16
    wceq
    #
    vi
    cab
    @22
    @20
    @6
    @23
    vi
    @20
    @6
    @16
    @1
    wceq
    #
    @23
    @20
    @6
    @24
    @20
    @6
    wa
    @0
    @17
    @2
    @19
    @5
    @24
    @0
    @17
    @19
    @6
    simplll
    @0
    @17
    @19
    @6
    simpllr
    @20
    @2
    @5
    simprl
    @18
    @19
    @6
    simplr
    @20
    @2
    @5
    simprr
    vx
    cA
    cB
    @4
    @1
    @3
    disjabrexf.1
    @15
    vx
    @1
    cB
    csbeq1a
    #
    disjif2
    syl122anc
    @20
    @24
    wa
    #
    @2
    @5
    @26
    @16
    @1
    cA
    @20
    @24
    simpr
    #
    @0
    @17
    @19
    @24
    simpllr
    eqeltrrd
    @26
    @19
    @5
    @18
    @19
    @24
    simplr
    @26
    @24
    @19
    @5
    wb
    @27
    @24
    cB
    @4
    @3
    @25
    eleq2d
    syl
    mpbid
    jca
    impbida
    vx
    vi
    equcom
    syl6bb
    abbidv
    vi
    @16
    df-sn
    syl6eqr
    unieqd
    @16
    vx
    vex
    unisn
    syl6eq
    @21
    @9
    vx
    @16
    cB
    csb
    cB
    vx
    @8
    @16
    cB
    csbeq1
    vx
    cB
    csbid
    syl6eq
    syl
    ralrimiva
    elabreximd
    ralrimiva
    vy
    vj
    @13
    @10
    @9
    invdisj
    syl
end
