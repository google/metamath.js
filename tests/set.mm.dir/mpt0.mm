include "c0.mm"
include "cmpt.mm"
include "wfn.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "ral0.mm"
include "eqid.mm"
include "fnmpt.mm"
include "ax-mp.mm"
include "fn0.mm"
include "mpbi.mm"

theorem mpt0
  let vx: setvar x
  let cA: class A


  assert |- ( x e. (/) |-> A ) = (/)

  proof
    vx
    c0
    cA
    cmpt
    #
    c0
    wfn
    #
    @0
    c0
    wceq
    cA
    cvv
    wcel
    #
    vx
    c0
    wral
    @1
    @2
    vx
    ral0
    vx
    c0
    cA
    @0
    cvv
    @0
    eqid
    fnmpt
    ax-mp
    @0
    fn0
    mpbi
end
