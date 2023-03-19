include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "wfun.mm"
include "imass2.mm"
include "crn.mm"
include "cin.mm"
include "funimacnv.mm"
include "sseq2d.mm"
include "inss1.mm"
include "sstr2.mm"
include "mpi.mm"
include "syl6bi.mm"
include "imp.mm"
include "sylan2.mm"

theorem funimass2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A C_ ( `' F " B ) ) -> ( F " A ) C_ B )

  proof
    cA
    cF
    ccnv
    cB
    cima
    #
    wss
    cF
    wfun
    #
    cF
    cA
    cima
    #
    cF
    @0
    cima
    #
    wss
    #
    @2
    cB
    wss
    #
    cA
    @0
    cF
    imass2
    @1
    @4
    @5
    @1
    @4
    @2
    cB
    cF
    crn
    #
    cin
    #
    wss
    #
    @5
    @1
    @3
    @7
    @2
    cB
    cF
    funimacnv
    sseq2d
    @8
    @7
    cB
    wss
    @5
    cB
    @6
    inss1
    @2
    @7
    cB
    sstr2
    mpi
    syl6bi
    imp
    sylan2
end
