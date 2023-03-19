include "cpcmp.mm"
include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "clocfin.mm"
include "cfv.mm"
include "cref.mm"
include "wbr.mm"
include "wa.mm"
include "wf.mm"
include "crn.mm"
include "wex.mm"
include "cpw.mm"
include "simpll2.mm"
include "simpll3.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "simprl.mm"
include "locfinref.mm"
include "pcmplfin.mm"
include "r19.29a.mm"

theorem pcmplfinf
  let cU: class U
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  assume pcmplfin.x: |- X = U. J

  disjoint J f
  disjoint U f
  disjoint X f
  disjoint J u
  disjoint J v
  disjoint u v
  disjoint U u
  disjoint U v
  disjoint X u
  disjoint X v
  disjoint f v
  assert |- ( ( J e. Paracomp /\ U C_ J /\ X = U. U ) -> E. f ( f : U --> J /\ ran f Ref U /\ ran f e. ( LocFin ` J ) ) )

  proof
    cJ
    cpcmp
    wcel
    #
    cU
    cJ
    wss
    #
    cX
    cU
    cuni
    wceq
    #
    w3a
    #
    vv
    cv
    #
    cJ
    clocfin
    cfv
    #
    wcel
    #
    @4
    cU
    cref
    wbr
    #
    wa
    #
    cU
    cJ
    vf
    cv
    #
    wf
    @9
    crn
    #
    cU
    cref
    wbr
    @10
    @5
    wcel
    w3a
    vf
    wex
    vv
    cJ
    cpw
    #
    @3
    @4
    @11
    wcel
    #
    wa
    #
    @8
    wa
    cU
    vf
    cJ
    @4
    cX
    pcmplfin.x
    @0
    @1
    @2
    @12
    @8
    simpll2
    @0
    @1
    @2
    @12
    @8
    simpll3
    @12
    @4
    cJ
    wss
    @3
    @8
    @4
    cJ
    elpwi
    ad2antlr
    @13
    @6
    @7
    simprr
    @13
    @6
    @7
    simprl
    locfinref
    vv
    cU
    cJ
    cX
    pcmplfin.x
    pcmplfin
    r19.29a
end
