include "chil.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "ffn.mm"
include "wa.mm"
include "eqfnfv.mm"
include "bicomd.mm"
include "syl2an.mm"

theorem hoeq
  let vx: setvar x
  let cT: class T
  let cU: class U

  disjoint T x
  disjoint U x
  assert |- ( ( T : ~H --> ~H /\ U : ~H --> ~H ) -> ( A. x e. ~H ( T ` x ) = ( U ` x ) <-> T = U ) )

  proof
    chil
    chil
    cT
    wf
    cT
    chil
    wfn
    #
    cU
    chil
    wfn
    #
    vx
    cv
    #
    cT
    cfv
    @2
    cU
    cfv
    wceq
    vx
    chil
    wral
    #
    cT
    cU
    wceq
    #
    wb
    chil
    chil
    cU
    wf
    chil
    chil
    cT
    ffn
    chil
    chil
    cU
    ffn
    @0
    @1
    wa
    @4
    @3
    vx
    chil
    cT
    cU
    eqfnfv
    bicomd
    syl2an
end
