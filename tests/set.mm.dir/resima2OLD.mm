include "wss.mm"
include "cres.mm"
include "cima.mm"
include "crn.mm"
include "df-ima.mm"
include "cin.mm"
include "resres.mm"
include "rneqi.mm"
include "wceq.mm"
include "df-ss.mm"
include "incom.mm"
include "a1i.mm"
include "reseq2d.mm"
include "rneqd.mm"
include "reseq2.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "sylbi.mm"
include "syl5eq.mm"

theorem resima2OLD
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B C_ C -> ( ( A |` C ) " B ) = ( A " B ) )

  proof
    cB
    cC
    wss
    #
    cA
    cC
    cres
    #
    cB
    cima
    @1
    cB
    cres
    #
    crn
    #
    cA
    cB
    cima
    #
    @1
    cB
    df-ima
    @0
    @3
    cA
    cC
    cB
    cin
    #
    cres
    #
    crn
    #
    @4
    @2
    @6
    cA
    cC
    cB
    resres
    rneqi
    @0
    cB
    cC
    cin
    #
    cB
    wceq
    #
    @7
    @4
    wceq
    cB
    cC
    df-ss
    @9
    @7
    cA
    @8
    cres
    #
    crn
    #
    @4
    @9
    @6
    @10
    @9
    @5
    @8
    cA
    @5
    @8
    wceq
    @9
    cC
    cB
    incom
    a1i
    reseq2d
    rneqd
    @9
    @11
    cA
    cB
    cres
    #
    crn
    @4
    @9
    @10
    @12
    @8
    cB
    cA
    reseq2
    rneqd
    cA
    cB
    df-ima
    syl6eqr
    eqtrd
    sylbi
    syl5eq
    syl5eq
end
