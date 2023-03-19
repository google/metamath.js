include "cprime.mm"
include "wcel.mm"
include "wa.mm"
include "ceven.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "codd.mm"
include "wi.mm"
include "cc.mm"
include "prmz.mm"
include "zcnd.mm"
include "addcom.mm"
include "syl2anr.mm"
include "eqeq2d.mm"
include "3anbi3d.mm"
include "sbgoldbaltlem1.mm"
include "sylbid.mm"
include "ancoms.mm"
include "jcad.mm"

theorem sbgoldbaltlem2
  let cP: class P
  let cQ: class Q
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P e. Prime /\ Q e. Prime ) -> ( ( N e. Even /\ 4 < N /\ N = ( P + Q ) ) -> ( P e. Odd /\ Q e. Odd ) ) )

  proof
    cP
    cprime
    wcel
    #
    cQ
    cprime
    wcel
    #
    wa
    cN
    ceven
    wcel
    #
    c4
    cN
    clt
    wbr
    #
    cN
    cP
    cQ
    caddc
    co
    #
    wceq
    #
    w3a
    #
    cP
    codd
    wcel
    #
    cQ
    codd
    wcel
    @1
    @0
    @6
    @7
    wi
    @1
    @0
    wa
    #
    @6
    @2
    @3
    cN
    cQ
    cP
    caddc
    co
    #
    wceq
    #
    w3a
    @7
    @8
    @5
    @10
    @2
    @3
    @8
    @4
    @9
    cN
    @0
    cP
    cc
    wcel
    cQ
    cc
    wcel
    @4
    @9
    wceq
    @1
    @0
    cP
    cP
    prmz
    zcnd
    @1
    cQ
    cQ
    prmz
    zcnd
    cP
    cQ
    addcom
    syl2anr
    eqeq2d
    3anbi3d
    cQ
    cP
    cN
    sbgoldbaltlem1
    sylbid
    ancoms
    cP
    cQ
    cN
    sbgoldbaltlem1
    jcad
end
