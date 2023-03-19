include "wfun.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "cdm.mm"
include "wrex.mm"
include "elfvdm.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "mpancom.mm"
include "adantl.mm"
include "wb.mm"
include "elunirn.mm"
include "adantr.mm"
include "mpbird.mm"

theorem elunirn2
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( ( Fun F /\ B e. ( F ` A ) ) -> B e. U. ran F )

  proof
    cF
    wfun
    #
    cB
    cA
    cF
    cfv
    #
    wcel
    #
    wa
    cB
    cF
    crn
    cuni
    wcel
    #
    cB
    vx
    cv
    #
    cF
    cfv
    #
    wcel
    #
    vx
    cF
    cdm
    #
    wrex
    #
    @2
    @8
    @0
    cA
    @7
    wcel
    @2
    @8
    cB
    cA
    cF
    elfvdm
    @6
    @2
    vx
    cA
    @7
    @4
    cA
    wceq
    @5
    @1
    cB
    @4
    cA
    cF
    fveq2
    eleq2d
    rspcev
    mpancom
    adantl
    @0
    @3
    @8
    wb
    @2
    vx
    cB
    cF
    elunirn
    adantr
    mpbird
end
