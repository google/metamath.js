include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cpi.mm"
include "cneg.mm"
include "cim.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "crn.mm"
include "logrncl.mm"
include "ellogrn.mm"
include "sylib.mm"
include "3simpc.mm"
include "syl.mm"

theorem logimcl
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( -u _pi < ( Im ` ( log ` A ) ) /\ ( Im ` ( log ` A ) ) <_ _pi ) )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    #
    cA
    clog
    cfv
    #
    cc
    wcel
    #
    cpi
    cneg
    @1
    cim
    cfv
    #
    clt
    wbr
    #
    @3
    cpi
    cle
    wbr
    #
    w3a
    #
    @4
    @5
    wa
    @0
    @1
    clog
    crn
    wcel
    @6
    cA
    logrncl
    @1
    ellogrn
    sylib
    @2
    @4
    @5
    3simpc
    syl
end
