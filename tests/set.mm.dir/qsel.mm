include "wer.mm"
include "cqs.mm"
include "wcel.mm"
include "cec.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "eqid.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elecg.mm"
include "mpan2.mm"
include "ibi.mm"
include "simpll.mm"
include "simpr.mm"
include "erthi.mm"
include "ex.mm"
include "syl5.mm"
include "ectocld.mm"
include "3impia.mm"

theorem qsel
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vx: setvar x


  assert |- ( ( R Er X /\ B e. ( A /. R ) /\ C e. B ) -> B = [ C ] R )

  proof
    cX
    cR
    wer
    #
    cB
    cA
    cR
    cqs
    #
    wcel
    cC
    cB
    wcel
    #
    cB
    cC
    cR
    cec
    #
    wceq
    #
    cC
    vx
    cv
    #
    cR
    cec
    #
    wcel
    #
    @6
    @3
    wceq
    #
    wi
    @2
    @4
    wi
    @0
    vx
    cB
    cA
    cR
    @1
    @1
    eqid
    @6
    cB
    wceq
    @7
    @2
    @8
    @4
    @6
    cB
    cC
    eleq2
    @6
    cB
    @3
    eqeq1
    imbi12d
    @7
    @5
    cC
    cR
    wbr
    #
    @0
    @5
    cA
    wcel
    #
    wa
    #
    @8
    @7
    @9
    @7
    @5
    cvv
    wcel
    @7
    @9
    wb
    vx
    vex
    cC
    @5
    cR
    @6
    cvv
    elecg
    mpan2
    ibi
    @11
    @9
    @8
    @11
    @9
    wa
    @5
    cC
    cR
    cX
    @0
    @10
    @9
    simpll
    @11
    @9
    simpr
    erthi
    ex
    syl5
    ectocld
    3impia
end
