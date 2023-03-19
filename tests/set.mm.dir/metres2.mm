include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "cr.mm"
include "wf.mm"
include "metxmet.mm"
include "xmetres2.mm"
include "sylan.mm"
include "metf.mm"
include "adantr.mm"
include "simpr.mm"
include "xpss12.mm"
include "sylancom.mm"
include "fssresd.mm"
include "ismet2.mm"
include "sylanbrc.mm"

theorem metres2
  let cD: class D
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cC: class C


  assert |- ( ( D e. ( Met ` X ) /\ R C_ X ) -> ( D |` ( R X. R ) ) e. ( Met ` R ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cR
    cX
    wss
    #
    wa
    #
    cD
    cR
    cR
    cxp
    #
    cres
    #
    cR
    cxmt
    cfv
    wcel
    #
    @3
    cr
    @4
    wf
    @4
    cR
    cme
    cfv
    wcel
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    @1
    @5
    cD
    cX
    metxmet
    cD
    cR
    cX
    xmetres2
    sylan
    @2
    cX
    cX
    cxp
    #
    cr
    @3
    cD
    @0
    @6
    cr
    cD
    wf
    @1
    cD
    cX
    metf
    adantr
    @0
    @1
    @1
    @3
    @6
    wss
    @0
    @1
    simpr
    cR
    cX
    cR
    cX
    xpss12
    sylancom
    fssresd
    @4
    cR
    ismet2
    sylanbrc
end
