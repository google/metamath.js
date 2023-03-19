include "wss.mm"
include "wrel.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "wa.mm"
include "wfun.mm"
include "relss.mm"
include "wi.mm"
include "coss1.mm"
include "cnvss.mm"
include "coss2.mm"
include "syl.mm"
include "sstrd.mm"
include "sstr2.mm"
include "anim12d.mm"
include "df-fun.mm"
include "3imtr4g.mm"

theorem funss
  let cA: class A
  let cB: class B


  assert |- ( A C_ B -> ( Fun B -> Fun A ) )

  proof
    cA
    cB
    wss
    #
    cB
    wrel
    #
    cB
    cB
    ccnv
    #
    ccom
    #
    cid
    wss
    #
    wa
    cA
    wrel
    #
    cA
    cA
    ccnv
    #
    ccom
    #
    cid
    wss
    #
    wa
    cB
    wfun
    cA
    wfun
    @0
    @1
    @5
    @4
    @8
    cA
    cB
    relss
    @0
    @7
    @3
    wss
    @4
    @8
    wi
    @0
    @7
    cB
    @6
    ccom
    #
    @3
    cA
    cB
    @6
    coss1
    @0
    @6
    @2
    wss
    @9
    @3
    wss
    cA
    cB
    cnvss
    @6
    @2
    cB
    coss2
    syl
    sstrd
    @7
    @3
    cid
    sstr2
    syl
    anim12d
    cB
    df-fun
    cA
    df-fun
    3imtr4g
end
