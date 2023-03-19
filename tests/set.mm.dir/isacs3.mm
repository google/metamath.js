include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmre.mm"
include "cv.mm"
include "cipo.mm"
include "cdrs.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "isacs3lem.mm"
include "cmrc.mm"
include "cima.mm"
include "wceq.mm"
include "eqid.mm"
include "isacs4lem.mm"
include "isacs4.mm"
include "sylibr.mm"
include "impbii.mm"

theorem isacs3
  let cC: class C
  let cX: class X
  let vs: setvar s
  let vt: setvar t

  disjoint C s
  disjoint X s
  disjoint C t
  disjoint s t
  disjoint X t
  assert |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\ A. s e. ~P C ( ( toInc ` s ) e. Dirset -> U. s e. C ) ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    #
    cC
    cX
    cmre
    cfv
    wcel
    #
    vs
    cv
    #
    cipo
    cfv
    cdrs
    wcel
    @2
    cuni
    cC
    wcel
    wi
    vs
    cC
    cpw
    wral
    wa
    #
    cC
    cX
    vs
    isacs3lem
    @3
    @1
    vt
    cv
    #
    cipo
    cfv
    cdrs
    wcel
    @4
    cuni
    cC
    cmrc
    cfv
    #
    cfv
    @5
    @4
    cima
    cuni
    wceq
    wi
    vt
    cX
    cpw
    cpw
    wral
    wa
    @0
    vt
    cC
    @5
    cX
    vs
    @5
    eqid
    #
    isacs4lem
    cC
    @5
    cX
    vt
    @6
    isacs4
    sylibr
    impbii
end
