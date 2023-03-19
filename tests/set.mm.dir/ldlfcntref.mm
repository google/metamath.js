include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cab.mm"
include "cldlf.mm"
include "df-ldlf.mm"
include "wcel.mm"
include "vex.mm"
include "breq1.mm"
include "elab.mm"
include "biimpi.mm"
include "crefdf.mm"

theorem ldlfcntref
  let vv: setvar v
  let cU: class U
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume ldlfcntref.x: |- X = U. J

  disjoint J v
  disjoint U v
  disjoint v x
  assert |- ( ( J e. Ldlf /\ U C_ J /\ X = U. U ) -> E. v e. ~P J ( v ~<_ _om /\ v Ref U ) )

  proof
    vv
    cv
    #
    com
    cdom
    wbr
    #
    vv
    vx
    cv
    #
    com
    cdom
    wbr
    #
    vx
    cab
    #
    cldlf
    cU
    cJ
    cX
    ldlfcntref.x
    vx
    df-ldlf
    @0
    @4
    wcel
    @1
    @3
    @1
    vx
    @0
    vv
    vex
    @2
    @0
    com
    cdom
    breq1
    elab
    biimpi
    crefdf
end
