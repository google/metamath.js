include "ctsk.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "c1o.mm"
include "csn.mm"
include "df1o2.mm"
include "tsk0.mm"
include "tsksn.mm"
include "syldan.mm"
include "syl5eqel.mm"

theorem tsk1
  let cT: class T


  assert |- ( ( T e. Tarski /\ T =/= (/) ) -> 1o e. T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    c0
    wne
    #
    wa
    c1o
    c0
    csn
    #
    cT
    df1o2
    @0
    @1
    c0
    cT
    wcel
    @2
    cT
    wcel
    cT
    tsk0
    c0
    cT
    tsksn
    syldan
    syl5eqel
end
