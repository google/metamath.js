include "ctsk.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "c2o.mm"
include "csdm.mm"
include "wbr.mm"
include "tsk2.mm"
include "tsksdom.mm"
include "syldan.mm"

theorem 2domtsk
  let cT: class T


  assert |- ( ( T e. Tarski /\ T =/= (/) ) -> 2o ~< T )

  proof
    cT
    ctsk
    wcel
    cT
    c0
    wne
    c2o
    cT
    wcel
    c2o
    cT
    csdm
    wbr
    cT
    tsk2
    c2o
    cT
    tsksdom
    syldan
end
