include "cpjh.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "pjclii.mm"
include "pjhclii.mm"
include "pjchi.mm"
include "mpbi.mm"

theorem pjidmi
  let cA: class A
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H


  assert |- ( ( projh ` H ) ` ( ( projh ` H ) ` A ) ) = ( ( projh ` H ) ` A )

  proof
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cH
    wcel
    @1
    @0
    cfv
    @1
    wceq
    cA
    cH
    pjidm.1
    pjidm.2
    pjclii
    @1
    cH
    pjidm.1
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    pjchi
    mpbi
end
