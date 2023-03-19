include "wcel.mm"
include "cid.mm"
include "wbr.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "id.mm"
include "reli.mm"
include "brrelexi.mm"
include "anim12ci.mm"
include "eleq1.mm"
include "biimparc.mm"
include "elexd.mm"
include "simpl.mm"
include "jca.mm"
include "cv.mm"
include "eqeq1.mm"
include "eqeq2.mm"
include "df-id.mm"
include "brabg.mm"
include "pm5.21nd.mm"

theorem ideqg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. V -> ( A _I B <-> A = B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    cid
    wbr
    #
    cA
    cB
    wceq
    #
    cA
    cvv
    wcel
    #
    @0
    wa
    @0
    @0
    @1
    @3
    @0
    id
    cA
    cB
    cid
    reli
    brrelexi
    anim12ci
    @0
    @2
    wa
    #
    @3
    @0
    @4
    cA
    cV
    @2
    cA
    cV
    wcel
    @0
    cA
    cB
    cV
    eleq1
    biimparc
    elexd
    @0
    @2
    simpl
    jca
    vx
    cv
    #
    vy
    cv
    #
    wceq
    cA
    @6
    wceq
    @2
    vx
    vy
    cA
    cB
    cvv
    cV
    cid
    @5
    cA
    @6
    eqeq1
    @6
    cB
    cA
    eqeq2
    vx
    vy
    df-id
    brabg
    pm5.21nd
end
