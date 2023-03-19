include "com.mm"
include "wcel.mm"
include "wpss.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "psseq2.mm"
include "anbi12d.mm"
include "breq2.mm"
include "imbi12d.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "cvv.mm"
include "wss.mm"
include "vex.mm"
include "pssss.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "adantl.mm"
include "php.mm"
include "ensym.mm"
include "nsyl.mm"
include "brsdom.mm"
include "sylanbrc.mm"
include "vtoclg.mm"
include "anabsi5.mm"

theorem php2
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B C. A ) -> B ~< A )

  proof
    cA
    com
    wcel
    #
    cB
    cA
    wpss
    #
    cB
    cA
    csdm
    wbr
    #
    vx
    cv
    #
    com
    wcel
    #
    cB
    @3
    wpss
    #
    wa
    #
    cB
    @3
    csdm
    wbr
    #
    wi
    @0
    @1
    wa
    #
    @2
    wi
    vx
    cA
    com
    @3
    cA
    wceq
    #
    @6
    @8
    @7
    @2
    @9
    @4
    @0
    @5
    @1
    @3
    cA
    com
    eleq1
    @3
    cA
    cB
    psseq2
    anbi12d
    @3
    cA
    cB
    csdm
    breq2
    imbi12d
    @6
    cB
    @3
    cdom
    wbr
    #
    cB
    @3
    cen
    wbr
    #
    wn
    @7
    @5
    @10
    @4
    @3
    cvv
    wcel
    @5
    cB
    @3
    wss
    @10
    vx
    vex
    cB
    @3
    pssss
    cB
    @3
    cvv
    ssdomg
    mpsyl
    adantl
    @6
    @3
    cB
    cen
    wbr
    @11
    @3
    cB
    php
    cB
    @3
    ensym
    nsyl
    cB
    @3
    brsdom
    sylanbrc
    vtoclg
    anabsi5
end
