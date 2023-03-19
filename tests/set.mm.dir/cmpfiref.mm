include "cv.mm"
include "cfn.mm"
include "wcel.mm"
include "ccmp.mm"
include "cmpcref.mm"
include "id.mm"
include "crefdf.mm"

theorem cmpfiref
  let vv: setvar v
  let cU: class U
  let cJ: class J
  let cX: class X
  assume cmpfiref.x: |- X = U. J

  disjoint J v
  disjoint U v
  assert |- ( ( J e. Comp /\ U C_ J /\ X = U. U ) -> E. v e. ~P J ( v e. Fin /\ v Ref U ) )

  proof
    vv
    cv
    cfn
    wcel
    #
    vv
    cfn
    ccmp
    cU
    cJ
    cX
    cmpfiref.x
    cmpcref
    @0
    id
    crefdf
end
