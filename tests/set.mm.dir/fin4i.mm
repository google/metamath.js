include "cfin4.mm"
include "wcel.mm"
include "cv.mm"
include "wpss.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "isfin4.mm"
include "ibi.mm"
include "cvv.mm"
include "relen.mm"
include "brrelexi.mm"
include "adantl.mm"
include "wceq.mm"
include "psseq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mpcom.mm"
include "nsyl3.mm"

theorem fin4i
  let cA: class A
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( X C. A /\ X ~~ A ) -> -. A e. Fin4 )

  proof
    cA
    cfin4
    wcel
    #
    vx
    cv
    #
    cA
    wpss
    #
    @1
    cA
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    cX
    cA
    wpss
    #
    cX
    cA
    cen
    wbr
    #
    wa
    #
    @0
    @5
    wn
    vx
    cA
    cfin4
    isfin4
    ibi
    cX
    cvv
    wcel
    #
    @8
    @5
    @7
    @9
    @6
    cX
    cA
    cen
    relen
    brrelexi
    adantl
    @4
    @8
    vx
    cX
    cvv
    @1
    cX
    wceq
    @2
    @6
    @3
    @7
    @1
    cX
    cA
    psseq1
    @1
    cX
    cA
    cen
    breq1
    anbi12d
    spcegv
    mpcom
    nsyl3
end
