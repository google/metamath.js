include "wcel.mm"
include "cs1.mm"
include "cc0.mm"
include "cid.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "df-s1.mm"
include "fvi.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "syl5eq.mm"

theorem s1val
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> <" A "> = { <. 0 , A >. } )

  proof
    cA
    cV
    wcel
    #
    cA
    cs1
    cc0
    cA
    cid
    cfv
    #
    cop
    #
    csn
    cc0
    cA
    cop
    #
    csn
    cA
    df-s1
    @0
    @2
    @3
    @0
    @1
    cA
    cc0
    cA
    cV
    fvi
    opeq2d
    sneqd
    syl5eq
end
