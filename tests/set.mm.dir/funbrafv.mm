include "wfun.mm"
include "wbr.mm"
include "cafv.mm"
include "wceq.mm"
include "wi.mm"
include "wrel.mm"
include "funrel.mm"
include "wa.mm"
include "cdm.mm"
include "wcel.mm"
include "releldm.mm"
include "funbrafvb.mm"
include "biimprd.mm"
include "expcom.mm"
include "syl.mm"
include "ex.mm"
include "com14.mm"
include "pm2.43i.mm"
include "com13.mm"

theorem funbrafv
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( Fun F -> ( A F B -> ( F ''' A ) = B ) )

  proof
    cF
    wfun
    #
    cA
    cB
    cF
    wbr
    #
    cA
    cF
    cafv
    cB
    wceq
    #
    wi
    #
    @0
    cF
    wrel
    #
    @0
    @3
    wi
    #
    cF
    funrel
    @1
    @0
    @4
    @2
    @1
    @0
    @4
    @2
    wi
    wi
    @4
    @1
    @0
    @1
    @2
    @4
    @1
    @5
    @4
    @1
    wa
    cA
    cF
    cdm
    wcel
    #
    @5
    cA
    cB
    cF
    releldm
    @0
    @6
    @3
    @0
    @6
    wa
    @2
    @1
    cA
    cB
    cF
    funbrafvb
    biimprd
    expcom
    syl
    ex
    com14
    pm2.43i
    com13
    syl
    pm2.43i
end
