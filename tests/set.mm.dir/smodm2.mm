include "wsmo.mm"
include "wfn.mm"
include "cdm.mm"
include "word.mm"
include "smodm.mm"
include "wceq.mm"
include "wb.mm"
include "fndm.mm"
include "ordeq.mm"
include "syl.mm"
include "biimpa.mm"
include "sylan2.mm"

theorem smodm2
  let cA: class A
  let cF: class F


  assert |- ( ( F Fn A /\ Smo F ) -> Ord A )

  proof
    cF
    wsmo
    cF
    cA
    wfn
    #
    cF
    cdm
    #
    word
    #
    cA
    word
    #
    cF
    smodm
    @0
    @2
    @3
    @0
    @1
    cA
    wceq
    @2
    @3
    wb
    cA
    cF
    fndm
    @1
    cA
    ordeq
    syl
    biimpa
    sylan2
end
