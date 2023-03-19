include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "cnvcnvsn.mm"
include "wrel.mm"
include "wceq.mm"
include "relsnop.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "eqtr3i.mm"

theorem cnvsnOLD
  let cA: class A
  let cB: class B
  assume cnvsn.1: |- A e. _V
  assume cnvsn.2: |- B e. _V


  assert |- `' { <. A , B >. } = { <. B , A >. }

  proof
    cB
    cA
    cop
    csn
    #
    ccnv
    ccnv
    #
    cA
    cB
    cop
    csn
    ccnv
    @0
    cB
    cA
    cnvcnvsn
    @0
    wrel
    @1
    @0
    wceq
    cB
    cA
    cnvsn.2
    cnvsn.1
    relsnop
    @0
    dfrel2
    mpbi
    eqtr3i
end
