include "cperf.mm"
include "wcel.mm"
include "ctop.mm"
include "clp.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "isperf.mm"
include "wb.mm"
include "ssid.mm"
include "lpss.mm"
include "mpan2.mm"
include "eqss.mm"
include "baib.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isperf2
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( J e. Perf <-> ( J e. Top /\ X C_ ( ( limPt ` J ) ` X ) ) )

  proof
    cJ
    cperf
    wcel
    cJ
    ctop
    wcel
    #
    cX
    cJ
    clp
    cfv
    cfv
    #
    cX
    wceq
    #
    wa
    @0
    cX
    @1
    wss
    #
    wa
    cJ
    cX
    lpfval.1
    isperf
    @0
    @2
    @3
    @0
    @1
    cX
    wss
    #
    @2
    @3
    wb
    @0
    cX
    cX
    wss
    @4
    cX
    ssid
    cX
    cJ
    cX
    lpfval.1
    lpss
    mpan2
    @2
    @4
    @3
    @1
    cX
    eqss
    baib
    syl
    pm5.32i
    bitri
end
