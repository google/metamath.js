include "com.mm"
include "cv.mm"
include "csuc.mm"
include "csn.mm"
include "co.mm"
include "cxp.mm"
include "cmpt2.mm"
include "eqid.mm"
include "axdc4lem.mm"

theorem axdc4
  let cA: class A
  let cC: class C
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let vn: setvar n
  let vx: setvar x
  assume axdc4.1: |- A e. _V

  disjoint A g
  disjoint A k
  disjoint g k
  disjoint C g
  disjoint C k
  disjoint F g
  disjoint F k
  disjoint A n
  disjoint A x
  disjoint g n
  disjoint g x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint F n
  disjoint F x
  assert |- ( ( C e. A /\ F : ( _om X. A ) --> ( ~P A \ { (/) } ) ) -> E. g ( g : _om --> A /\ ( g ` (/) ) = C /\ A. k e. _om ( g ` suc k ) e. ( k F ( g ` k ) ) ) )

  proof
    vx
    cA
    cC
    vg
    vk
    vn
    cF
    vn
    vx
    com
    cA
    vn
    cv
    #
    csuc
    csn
    @0
    vx
    cv
    cF
    co
    cxp
    cmpt2
    #
    axdc4.1
    @1
    eqid
    axdc4lem
end
