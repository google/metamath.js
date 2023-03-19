include "c0.mm"
include "ctsk.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "ral0.mm"
include "csn.mm"
include "wceq.mm"
include "elsni.mm"
include "0ex.mm"
include "enref.mm"
include "breq1.mm"
include "mpbiri.mm"
include "orcd.mm"
include "syl.mm"
include "pw0.mm"
include "eleq2s.mm"
include "rgen.mm"
include "cvv.mm"
include "wb.mm"
include "eltsk2g.mm"
include "ax-mp.mm"
include "mpbir2an.mm"

theorem 0tsk
  let vx: setvar x


  assert |- (/) e. Tarski

  proof
    c0
    ctsk
    wcel
    #
    vx
    cv
    #
    cpw
    #
    c0
    wss
    @2
    c0
    wcel
    wa
    #
    vx
    c0
    wral
    #
    @1
    c0
    cen
    wbr
    #
    @1
    c0
    wcel
    #
    wo
    #
    vx
    c0
    cpw
    #
    wral
    #
    @3
    vx
    ral0
    @7
    vx
    @8
    @7
    @1
    c0
    csn
    #
    @8
    @1
    @10
    wcel
    @1
    c0
    wceq
    #
    @7
    @1
    c0
    elsni
    @11
    @5
    @6
    @11
    @5
    c0
    c0
    cen
    wbr
    c0
    0ex
    enref
    @1
    c0
    c0
    cen
    breq1
    mpbiri
    orcd
    syl
    pw0
    eleq2s
    rgen
    c0
    cvv
    wcel
    @0
    @4
    @9
    wa
    wb
    0ex
    vx
    c0
    cvv
    eltsk2g
    ax-mp
    mpbir2an
end
