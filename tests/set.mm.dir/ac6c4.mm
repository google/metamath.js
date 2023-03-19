include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "ciun.mm"
include "wrex.mm"
include "wf.mm"
include "cfv.mm"
include "wa.mm"
include "wex.mm"
include "wfn.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfne.mm"
include "weq.mm"
include "csbeq1a.mm"
include "neeq1d.mm"
include "cbvral.mm"
include "n0.mm"
include "nfre1.mm"
include "nfel2.mm"
include "eleq2d.mm"
include "rspce.mm"
include "eliun.mm"
include "sylibr.mm"
include "rspe.mm"
include "sylancom.mm"
include "ex.mm"
include "exlimd.mm"
include "syl5bi.mm"
include "ralimia.mm"
include "sylbi.mm"
include "iunex.mm"
include "eleq1.mm"
include "ac6.mm"
include "ffn.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "biimpri.mm"
include "anim12i.mm"
include "eximi.mm"
include "3syl.mm"

theorem ac6c4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  assume ac6c4.1: |- A e. _V
  assume ac6c4.2: |- B e. _V

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint B f
  disjoint A y
  disjoint A z
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- ( A. x e. A B =/= (/) -> E. f ( f Fn A /\ A. x e. A ( f ` x ) e. B ) )

  proof
    cB
    c0
    wne
    #
    vx
    cA
    wral
    #
    vy
    cv
    #
    vx
    vz
    cv
    #
    cB
    csb
    #
    wcel
    #
    vy
    vx
    cA
    cB
    ciun
    #
    wrex
    #
    vz
    cA
    wral
    #
    cA
    @6
    vf
    cv
    #
    wf
    #
    @3
    @9
    cfv
    #
    @4
    wcel
    #
    vz
    cA
    wral
    #
    wa
    #
    vf
    wex
    @9
    cA
    wfn
    #
    vx
    cv
    #
    @9
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    @1
    @4
    c0
    wne
    #
    vz
    cA
    wral
    @8
    @0
    @21
    vx
    vz
    cA
    @0
    vz
    nfv
    vx
    @4
    c0
    vx
    @3
    cB
    nfcsb1v
    #
    vx
    c0
    nfcv
    nfne
    vx
    vz
    weq
    #
    cB
    @4
    c0
    vx
    @3
    cB
    csbeq1a
    #
    neeq1d
    cbvral
    @21
    @7
    vz
    cA
    @21
    @5
    vy
    wex
    @3
    cA
    wcel
    #
    @7
    vy
    @4
    n0
    @25
    @5
    @7
    vy
    @25
    vy
    nfv
    @5
    vy
    @6
    nfre1
    @25
    @5
    @7
    @25
    @5
    @2
    @6
    wcel
    #
    @7
    @25
    @5
    wa
    @2
    cB
    wcel
    #
    vx
    cA
    wrex
    @26
    @27
    @5
    vx
    @3
    cA
    vx
    @2
    @4
    @22
    nfel2
    @23
    cB
    @4
    @2
    @24
    eleq2d
    rspce
    vx
    @2
    cA
    cB
    eliun
    sylibr
    @5
    vy
    @6
    rspe
    sylancom
    ex
    exlimd
    syl5bi
    ralimia
    sylbi
    @5
    @12
    vz
    vy
    cA
    @6
    vf
    ac6c4.1
    vx
    cA
    cB
    ac6c4.1
    ac6c4.2
    iunex
    @2
    @11
    @4
    eleq1
    ac6
    @14
    @20
    vf
    @10
    @15
    @13
    @19
    cA
    @6
    @9
    ffn
    @19
    @13
    @18
    @12
    vx
    vz
    cA
    @18
    vz
    nfv
    vx
    @11
    @4
    @22
    nfel2
    @23
    @17
    @11
    cB
    @4
    @16
    @3
    @9
    fveq2
    @24
    eleq12d
    cbvral
    biimpri
    anim12i
    eximi
    3syl
end
