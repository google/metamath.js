include "wfo.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "wral.mm"
include "dffo2.mm"
include "cab.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fnrnfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfv.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "cbvrex.mm"
include "abbii.mm"
include "a1i.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "syl.mm"
include "wcel.mm"
include "wal.mm"
include "wi.mm"
include "nff.mm"
include "simpr.mm"
include "ffvelrn.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "exp31.mm"
include "rexlimd.mm"
include "biantrurd.mm"
include "dfbi2.mm"
include "syl6rbbr.mm"
include "albidv.mm"
include "abeq1.mm"
include "df-ral.mm"
include "3bitr4g.mm"
include "bitrd.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem dffo3f
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  assume dffo3f.1: |- F/_ x F

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F y
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint F w
  assert |- ( F : A -onto-> B <-> ( F : A --> B /\ A. y e. B E. x e. A y = ( F ` x ) ) )

  proof
    cA
    cB
    cF
    wfo
    cA
    cB
    cF
    wf
    #
    cF
    crn
    #
    cB
    wceq
    #
    wa
    @0
    vy
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    #
    wa
    cA
    cB
    cF
    dffo2
    @0
    @2
    @8
    @0
    @2
    @7
    vy
    cab
    #
    cB
    wceq
    #
    @8
    @0
    cF
    cA
    wfn
    #
    @2
    @10
    wb
    cA
    cB
    cF
    ffn
    @11
    @1
    @9
    cB
    @11
    @1
    @3
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vw
    cA
    wrex
    #
    vy
    cab
    #
    @9
    vw
    vy
    cA
    cF
    fnrnfv
    @16
    @9
    wceq
    @11
    @15
    @7
    vy
    @14
    @6
    vw
    vx
    cA
    vx
    @3
    @13
    vx
    @3
    nfcv
    vx
    @12
    cF
    dffo3f.1
    vx
    @12
    nfcv
    nffv
    nfeq
    @6
    vw
    nfv
    @12
    @4
    wceq
    @13
    @5
    @3
    @12
    @4
    cF
    fveq2
    eqeq2d
    cbvrex
    abbii
    a1i
    eqtrd
    eqeq1d
    syl
    @0
    @7
    @3
    cB
    wcel
    #
    wb
    #
    vy
    wal
    @17
    @7
    wi
    #
    vy
    wal
    @10
    @8
    @0
    @18
    @19
    vy
    @0
    @19
    @7
    @17
    wi
    #
    @19
    wa
    @18
    @0
    @20
    @19
    @0
    @6
    @17
    vx
    cA
    vx
    cA
    cB
    cF
    dffo3f.1
    vx
    cA
    nfcv
    vx
    cB
    nfcv
    nff
    @17
    vx
    nfv
    @0
    @4
    cA
    wcel
    #
    @6
    @17
    @0
    @21
    wa
    #
    @6
    wa
    @3
    @5
    cB
    @22
    @6
    simpr
    @22
    @5
    cB
    wcel
    @6
    cA
    cB
    @4
    cF
    ffvelrn
    adantr
    eqeltrd
    exp31
    rexlimd
    biantrurd
    @7
    @17
    dfbi2
    syl6rbbr
    albidv
    @7
    vy
    cB
    abeq1
    @7
    vy
    cB
    df-ral
    3bitr4g
    bitrd
    pm5.32i
    bitri
end
