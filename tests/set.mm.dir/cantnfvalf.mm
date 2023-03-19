include "com.mm"
include "con0.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "coa.mm"
include "co.mm"
include "cmpt2.mm"
include "c0.mm"
include "fnseqom.mm"
include "wceq.mm"
include "csuc.mm"
include "wrex.mm"
include "wo.mm"
include "nn0suc.mm"
include "fveq2.mm"
include "cvv.mm"
include "0ex.mm"
include "seqom0g.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "0elon.mm"
include "syl6eqel.mm"
include "cop.mm"
include "seqomsuc.mm"
include "df-ov.mm"
include "cxp.mm"
include "fnoa.mm"
include "oacl.mm"
include "rgen2a.mm"
include "ffnov.mm"
include "mpbir2an.mm"
include "f0cli.mm"
include "eqeltri.mm"
include "rgen2w.mm"
include "eqid.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "jaoi.mm"
include "syl.mm"
include "rgen.mm"
include "ffnfv.mm"

theorem cantnfvalf
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume cantnfvalf.f: |- F = seqom ( ( k e. A , z e. B |-> ( C +o D ) ) , (/) )

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint B k
  disjoint B z
  disjoint x y
  disjoint F x
  disjoint F y
  assert |- F : _om --> On

  proof
    com
    con0
    cF
    wf
    cF
    com
    wfn
    vx
    cv
    #
    cF
    cfv
    #
    con0
    wcel
    #
    vx
    com
    wral
    vk
    vz
    cA
    cB
    cC
    cD
    coa
    co
    #
    cmpt2
    #
    cF
    c0
    cantnfvalf.f
    fnseqom
    @2
    vx
    com
    @0
    com
    wcel
    @0
    c0
    wceq
    #
    @0
    vy
    cv
    #
    csuc
    #
    wceq
    #
    vy
    com
    wrex
    #
    wo
    @2
    vy
    @0
    nn0suc
    @5
    @2
    @9
    @5
    @1
    c0
    con0
    @5
    @1
    c0
    cF
    cfv
    #
    c0
    @0
    c0
    cF
    fveq2
    c0
    cvv
    wcel
    @10
    c0
    wceq
    0ex
    @4
    cF
    c0
    cvv
    cantnfvalf.f
    seqom0g
    ax-mp
    syl6eq
    0elon
    syl6eqel
    @8
    @2
    vy
    com
    @6
    com
    wcel
    #
    @2
    @8
    @7
    cF
    cfv
    #
    con0
    wcel
    @11
    @12
    @6
    @6
    cF
    cfv
    #
    cop
    #
    @4
    cfv
    #
    con0
    @11
    @12
    @6
    @13
    @4
    co
    @15
    @6
    @4
    cF
    c0
    cantnfvalf.f
    seqomsuc
    @6
    @13
    @4
    df-ov
    syl6eq
    cA
    cB
    cxp
    #
    con0
    @14
    @4
    @3
    con0
    wcel
    #
    vz
    cB
    wral
    vk
    cA
    wral
    @16
    con0
    @4
    wf
    @17
    vk
    vz
    cA
    cB
    @3
    cC
    cD
    cop
    #
    coa
    cfv
    con0
    cC
    cD
    coa
    df-ov
    con0
    con0
    cxp
    #
    con0
    @18
    coa
    @19
    con0
    coa
    wf
    coa
    @19
    wfn
    @0
    @6
    coa
    co
    con0
    wcel
    #
    vy
    con0
    wral
    vx
    con0
    wral
    fnoa
    @20
    vx
    vy
    con0
    @0
    @6
    oacl
    rgen2a
    vx
    vy
    con0
    con0
    con0
    coa
    ffnov
    mpbir2an
    0elon
    f0cli
    eqeltri
    rgen2w
    vk
    vz
    cA
    cB
    @3
    con0
    @4
    @4
    eqid
    fmpt2
    mpbi
    0elon
    f0cli
    syl6eqel
    @8
    @1
    @12
    con0
    @0
    @7
    cF
    fveq2
    eleq1d
    syl5ibrcom
    rexlimiv
    jaoi
    syl
    rgen
    vx
    com
    con0
    cF
    ffnfv
    mpbir2an
end
