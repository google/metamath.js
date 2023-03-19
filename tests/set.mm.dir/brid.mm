include "cid.mm"
include "wbr.mm"
include "ccnv.mm"
include "cnvi.mm"
include "breqi.mm"
include "reli.mm"
include "relbrcnv.mm"
include "bitr3i.mm"

theorem brid
  let cA: class A
  let cB: class B


  assert |- ( A _I B <-> B _I A )

  proof
    cA
    cB
    cid
    wbr
    cA
    cB
    cid
    ccnv
    #
    wbr
    cB
    cA
    cid
    wbr
    cA
    cB
    @0
    cid
    cnvi
    breqi
    cA
    cB
    cid
    reli
    relbrcnv
    bitr3i
end
