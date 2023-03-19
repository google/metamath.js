include "wcel.mm"
include "wf.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "w3a.mm"
include "crn.mm"
include "wss.mm"
include "cint.mm"
include "cfi.mm"
include "cfv.mm"
include "wa.mm"
include "simpr1.mm"
include "frn.mm"
include "syl.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "simpr2.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "wfo.mm"
include "simpr3.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "syl2anc.mm"
include "3jca.mm"
include "elfir.mm"
include "syldan.mm"

theorem intrnfi
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cW: class W


  assert |- ( ( B e. V /\ ( F : A --> B /\ A =/= (/) /\ A e. Fin ) ) -> |^| ran F e. ( fi ` B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    cF
    wf
    #
    cA
    c0
    wne
    #
    cA
    cfn
    wcel
    #
    w3a
    #
    cF
    crn
    #
    cB
    wss
    #
    @5
    c0
    wne
    #
    @5
    cfn
    wcel
    #
    w3a
    @5
    cint
    cB
    cfi
    cfv
    wcel
    @0
    @4
    wa
    #
    @6
    @7
    @8
    @9
    @1
    @6
    @0
    @1
    @2
    @3
    simpr1
    #
    cA
    cB
    cF
    frn
    syl
    @9
    cF
    cdm
    #
    c0
    wne
    @7
    @9
    @11
    cA
    c0
    @9
    @1
    @11
    cA
    wceq
    @10
    cA
    cB
    cF
    fdm
    syl
    @0
    @1
    @2
    @3
    simpr2
    eqnetrd
    @11
    c0
    @5
    c0
    cF
    dm0rn0
    necon3bii
    sylib
    @9
    @3
    cA
    @5
    cF
    wfo
    #
    @8
    @0
    @1
    @2
    @3
    simpr3
    @9
    cF
    cA
    wfn
    #
    @12
    @9
    @1
    @13
    @10
    cA
    cB
    cF
    ffn
    syl
    cA
    cF
    dffn4
    sylib
    cA
    @5
    cF
    fofi
    syl2anc
    3jca
    @5
    cB
    cV
    elfir
    syldan
end
