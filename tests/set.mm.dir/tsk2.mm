include "ctsk.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "c1o.mm"
include "c2o.mm"
include "tsk1.mm"
include "wa.mm"
include "csuc.mm"
include "df-2o.mm"
include "con0.mm"
include "1on.mm"
include "tsksuc.mm"
include "mp3an2.mm"
include "syl5eqel.mm"
include "syldan.mm"

theorem tsk2
  let cT: class T


  assert |- ( ( T e. Tarski /\ T =/= (/) ) -> 2o e. T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    c0
    wne
    c1o
    cT
    wcel
    #
    c2o
    cT
    wcel
    cT
    tsk1
    @0
    @1
    wa
    c2o
    c1o
    csuc
    #
    cT
    df-2o
    @0
    c1o
    con0
    wcel
    @1
    @2
    cT
    wcel
    1on
    c1o
    cT
    tsksuc
    mp3an2
    syl5eqel
    syldan
end
