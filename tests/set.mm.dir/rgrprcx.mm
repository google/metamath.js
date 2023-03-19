include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cvtx.mm"
include "wral.mm"
include "cab.mm"
include "cvv.mm"
include "wnel.mm"
include "crgr.mm"
include "wbr.mm"
include "rgrprc.mm"
include "wb.mm"
include "cxnn0.mm"
include "wcel.mm"
include "0xnn0.mm"
include "wa.mm"
include "vex.mm"
include "eqid.mm"
include "isrgr.mm"
include "mp2an.mm"
include "mpbiran.mm"
include "bicomi.mm"
include "abbii.mm"
include "neleq1.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem rgrprcx
  let vv: setvar v
  let vg: setvar g
  let ve: setvar e
  let vp: setvar p

  disjoint g v
  disjoint e g
  disjoint e p
  disjoint e v
  disjoint g p
  disjoint p v
  assert |- { g | A. v e. ( Vtx ` g ) ( ( VtxDeg ` g ) ` v ) = 0 } e/ _V

  proof
    vv
    cv
    vg
    cv
    #
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    vv
    @0
    cvtx
    cfv
    #
    wral
    #
    vg
    cab
    #
    cvv
    wnel
    #
    @0
    cc0
    crgr
    wbr
    #
    vg
    cab
    #
    cvv
    wnel
    #
    vg
    rgrprc
    @4
    @7
    wceq
    @5
    @8
    wb
    @3
    @6
    vg
    @6
    @3
    @6
    cc0
    cxnn0
    wcel
    #
    @3
    0xnn0
    @0
    cvv
    wcel
    @9
    @6
    @9
    @3
    wa
    wb
    vg
    vex
    0xnn0
    vv
    @1
    @0
    cc0
    @2
    cvv
    cxnn0
    @2
    eqid
    @1
    eqid
    isrgr
    mp2an
    mpbiran
    bicomi
    abbii
    @4
    @7
    cvv
    neleq1
    ax-mp
    mpbir
end
