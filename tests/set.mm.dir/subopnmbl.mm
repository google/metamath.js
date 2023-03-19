include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wrex.mm"
include "crest.mm"
include "co.mm"
include "eleq2i.mm"
include "ctop.mm"
include "wb.mm"
include "retop.mm"
include "elrest.mm"
include "mpan.mm"
include "syl5bb.mm"
include "wa.mm"
include "wi.mm"
include "opnmbl.mm"
include "id.mm"
include "inmbl.mm"
include "syl2anr.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "imp.mm"

theorem subopnmbl
  let cA: class A
  let cB: class B
  let cJ: class J
  let vx: setvar x
  assume subopnmbl.1: |- J = ( ( topGen ` ran (,) ) |`t A )


  assert |- ( ( A e. dom vol /\ B e. J ) -> B e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    cJ
    wcel
    #
    cB
    @0
    wcel
    #
    @1
    @2
    cB
    vx
    cv
    #
    cA
    cin
    #
    wceq
    #
    vx
    cioo
    crn
    ctg
    cfv
    #
    wrex
    #
    @3
    @2
    cB
    @7
    cA
    crest
    co
    #
    wcel
    #
    @1
    @8
    cJ
    @9
    cB
    subopnmbl.1
    eleq2i
    @7
    ctop
    wcel
    @1
    @10
    @8
    wb
    retop
    vx
    cB
    cA
    @7
    ctop
    @0
    elrest
    mpan
    syl5bb
    @1
    @6
    @3
    vx
    @7
    @1
    @4
    @7
    wcel
    #
    wa
    @5
    @0
    wcel
    #
    @6
    @3
    wi
    @11
    @4
    @0
    wcel
    @1
    @12
    @1
    @4
    opnmbl
    @1
    id
    @4
    cA
    inmbl
    syl2anr
    @5
    @0
    cB
    eleq1a
    syl
    rexlimdva
    sylbid
    imp
end
