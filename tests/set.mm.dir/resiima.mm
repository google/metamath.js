include "wss.mm"
include "cid.mm"
include "cres.mm"
include "cima.mm"
include "crn.mm"
include "wceq.mm"
include "df-ima.mm"
include "a1i.mm"
include "resabs1.mm"
include "rneqd.mm"
include "rnresi.mm"
include "3eqtrd.mm"

theorem resiima
  let cA: class A
  let cB: class B


  assert |- ( B C_ A -> ( ( _I |` A ) " B ) = B )

  proof
    cB
    cA
    wss
    #
    cid
    cA
    cres
    #
    cB
    cima
    #
    @1
    cB
    cres
    #
    crn
    #
    cid
    cB
    cres
    #
    crn
    #
    cB
    @2
    @4
    wceq
    @0
    @1
    cB
    df-ima
    a1i
    @0
    @3
    @5
    cid
    cB
    cA
    resabs1
    rneqd
    @6
    cB
    wceq
    @0
    cB
    rnresi
    a1i
    3eqtrd
end
