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
include "eqeq1d.mm"
include "syl.mm"
include "wcel.mm"
include "wal.mm"
include "wi.mm"
include "simpr.mm"
include "ffvelrn.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "exp31.mm"
include "rexlimdv.mm"
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

theorem dffo3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B z
  disjoint F z
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
    vx
    vy
    cA
    cF
    fnrnfv
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
    @12
    @7
    wi
    #
    vy
    wal
    @10
    @8
    @0
    @13
    @14
    vy
    @0
    @14
    @7
    @12
    wi
    #
    @14
    wa
    @13
    @0
    @15
    @14
    @0
    @6
    @12
    vx
    cA
    @0
    @4
    cA
    wcel
    #
    @6
    @12
    @0
    @16
    wa
    #
    @6
    wa
    @3
    @5
    cB
    @17
    @6
    simpr
    @17
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
    rexlimdv
    biantrurd
    @7
    @12
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
