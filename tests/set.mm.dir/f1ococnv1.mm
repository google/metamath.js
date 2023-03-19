include "wf1o.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wrel.mm"
include "wceq.mm"
include "f1orel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "coeq2d.mm"
include "f1ocnv.mm"
include "f1ococnv2.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem f1ococnv1
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> ( `' F o. F ) = ( _I |` A ) )

  proof
    cA
    cB
    cF
    wf1o
    #
    cF
    ccnv
    #
    @1
    ccnv
    #
    ccom
    #
    @1
    cF
    ccom
    cid
    cA
    cres
    #
    @0
    @2
    cF
    @1
    @0
    cF
    wrel
    @2
    cF
    wceq
    cA
    cB
    cF
    f1orel
    cF
    dfrel2
    sylib
    coeq2d
    @0
    cB
    cA
    @1
    wf1o
    @3
    @4
    wceq
    cA
    cB
    cF
    f1ocnv
    cB
    cA
    @1
    f1ococnv2
    syl
    eqtr3d
end
