include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cfg.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "fbelss.mm"
include "ex.mm"
include "wi.mm"
include "ssid.mm"
include "sseq1.mm"
include "rspcev.mm"
include "mpan2.mm"
include "a1i.mm"
include "jcad.mm"
include "elfg.mm"
include "sylibrd.mm"
include "ssrdv.mm"

theorem ssfg
  let cF: class F
  let cX: class X
  let vt: setvar t
  let vx: setvar x


  assert |- ( F e. ( fBas ` X ) -> F C_ ( X filGen F ) )

  proof
    cF
    cX
    cfbas
    cfv
    wcel
    #
    vt
    cF
    cX
    cF
    cfg
    co
    #
    @0
    vt
    cv
    #
    cF
    wcel
    #
    @2
    cX
    wss
    #
    vx
    cv
    #
    @2
    wss
    #
    vx
    cF
    wrex
    #
    wa
    @2
    @1
    wcel
    @0
    @3
    @4
    @7
    @0
    @3
    @4
    cX
    cF
    @2
    fbelss
    ex
    @3
    @7
    wi
    @0
    @3
    @2
    @2
    wss
    #
    @7
    @2
    ssid
    @6
    @8
    vx
    @2
    cF
    @5
    @2
    @2
    sseq1
    rspcev
    mpan2
    a1i
    jcad
    vx
    @2
    cF
    cX
    elfg
    sylibrd
    ssrdv
end
