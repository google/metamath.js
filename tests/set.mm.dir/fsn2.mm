include "csn.mm"
include "wf.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "snid.mm"
include "ffvelrn.mm"
include "mpan2.mm"
include "wfn.mm"
include "ffn.mm"
include "crn.mm"
include "dffn3.mm"
include "biimpi.mm"
include "cima.mm"
include "cdm.mm"
include "imadmrn.mm"
include "fndm.mm"
include "imaeq2d.mm"
include "syl5eqr.mm"
include "fnsnfv.mm"
include "eqtr4d.mm"
include "feq3d.mm"
include "mpbid.mm"
include "syl.mm"
include "jca.mm"
include "wss.mm"
include "snssi.mm"
include "fss.mm"
include "ancoms.mm"
include "sylan.mm"
include "impbii.mm"
include "fvex.mm"
include "fsn.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem fsn2
  let cA: class A
  let cB: class B
  let cF: class F
  assume fsn2.1: |- A e. _V


  assert |- ( F : { A } --> B <-> ( ( F ` A ) e. B /\ F = { <. A , ( F ` A ) >. } ) )

  proof
    cA
    csn
    #
    cB
    cF
    wf
    #
    cA
    cF
    cfv
    #
    cB
    wcel
    #
    @0
    @2
    csn
    #
    cF
    wf
    #
    wa
    #
    @3
    cF
    cA
    @2
    cop
    csn
    wceq
    #
    wa
    @1
    @6
    @1
    @3
    @5
    @1
    cA
    @0
    wcel
    #
    @3
    cA
    fsn2.1
    snid
    #
    @0
    cB
    cA
    cF
    ffvelrn
    mpan2
    @1
    cF
    @0
    wfn
    #
    @5
    @0
    cB
    cF
    ffn
    @10
    @0
    cF
    crn
    #
    cF
    wf
    #
    @5
    @10
    @12
    @0
    cF
    dffn3
    biimpi
    @10
    @11
    @4
    cF
    @0
    @10
    @11
    cF
    @0
    cima
    #
    @4
    @10
    @11
    cF
    cF
    cdm
    #
    cima
    @13
    cF
    imadmrn
    @10
    @14
    @0
    cF
    @0
    cF
    fndm
    imaeq2d
    syl5eqr
    @10
    @8
    @4
    @13
    wceq
    @9
    @0
    cA
    cF
    fnsnfv
    mpan2
    eqtr4d
    feq3d
    mpbid
    syl
    jca
    @3
    @4
    cB
    wss
    #
    @5
    @1
    @2
    cB
    snssi
    @5
    @15
    @1
    @0
    @4
    cB
    cF
    fss
    ancoms
    sylan
    impbii
    @5
    @7
    @3
    cA
    @2
    cF
    fsn2.1
    cA
    cF
    fvex
    fsn
    anbi2i
    bitri
end
