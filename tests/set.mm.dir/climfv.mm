include "cli.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "id.mm"
include "cdm.mm"
include "wcel.mm"
include "cvv.mm"
include "wrel.mm"
include "climrel.mm"
include "a1i.mm"
include "brrelex.mm"
include "syl2anc.mm"
include "brrelex2.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "climdm.mm"
include "sylib.mm"
include "climuni.mm"

theorem climfv
  let cA: class A
  let cF: class F


  assert |- ( F ~~> A -> A = ( ~~> ` F ) )

  proof
    cF
    cA
    cli
    wbr
    #
    @0
    cF
    cF
    cli
    cfv
    #
    cli
    wbr
    #
    cA
    @1
    wceq
    @0
    id
    #
    @0
    cF
    cli
    cdm
    wcel
    #
    @2
    @0
    cF
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @0
    @4
    @0
    cli
    wrel
    #
    @0
    @5
    @7
    @0
    climrel
    a1i
    #
    @3
    cF
    cA
    cli
    brrelex
    syl2anc
    @0
    @7
    @0
    @6
    @8
    @3
    cF
    cA
    cli
    brrelex2
    syl2anc
    @3
    cF
    cA
    cvv
    cvv
    cli
    breldmg
    syl3anc
    cF
    climdm
    sylib
    cA
    @1
    cF
    climuni
    syl2anc
end
