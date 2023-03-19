include "cfn.mm"
include "wcel.mm"
include "wf1.mm"
include "wa.mm"
include "crn.mm"
include "ccnv.mm"
include "wfo.mm"
include "wss.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "ssfi.mm"
include "sylan2.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "adantl.mm"
include "f1ocnv.mm"
include "f1ofo.mm"
include "3syl.mm"
include "fofi.mm"
include "syl2anc.mm"

theorem f1fi
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( B e. Fin /\ F : A -1-1-> B ) -> A e. Fin )

  proof
    cB
    cfn
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    wa
    #
    cF
    crn
    #
    cfn
    wcel
    #
    @3
    cA
    cF
    ccnv
    #
    wfo
    #
    cA
    cfn
    wcel
    @1
    @0
    @3
    cB
    wss
    #
    @4
    @1
    cA
    cB
    cF
    wf
    @7
    cA
    cB
    cF
    f1f
    cA
    cB
    cF
    frn
    syl
    cB
    @3
    ssfi
    sylan2
    @2
    cA
    @3
    cF
    wf1o
    #
    @3
    cA
    @5
    wf1o
    @6
    @1
    @8
    @0
    cA
    cB
    cF
    f1f1orn
    adantl
    cA
    @3
    cF
    f1ocnv
    @3
    cA
    @5
    f1ofo
    3syl
    @3
    cA
    @5
    fofi
    syl2anc
end
