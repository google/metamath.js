include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "crn.mm"
include "cfv.mm"
include "wceq.mm"
include "ce.mm"
include "wb.mm"
include "cr.mm"
include "rpcnne0.mm"
include "relogrn.mm"
include "logeftb.mm"
include "3expa.mm"
include "syl2an.mm"

theorem relogeftb
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR ) -> ( ( log ` A ) = B <-> ( exp ` B ) = A ) )

  proof
    cA
    crp
    wcel
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    cB
    clog
    crn
    wcel
    #
    cA
    clog
    cfv
    cB
    wceq
    cB
    ce
    cfv
    cA
    wceq
    wb
    #
    cB
    cr
    wcel
    cA
    rpcnne0
    cB
    relogrn
    @0
    @1
    @2
    @3
    cA
    cB
    logeftb
    3expa
    syl2an
end
