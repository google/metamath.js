include "wfun.mm"
include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "w3a.mm"
include "cres.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "funres.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "finresfin.mm"
include "3ad2ant2.mm"
include "hashfun.mm"
include "syl.mm"
include "mpbid.mm"
include "ssdmres.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem hashres
  let cA: class A
  let cB: class B


  assert |- ( ( Fun A /\ A e. Fin /\ B C_ dom A ) -> ( # ` ( A |` B ) ) = ( # ` B ) )

  proof
    cA
    wfun
    #
    cA
    cfn
    wcel
    #
    cB
    cA
    cdm
    wss
    #
    w3a
    #
    cA
    cB
    cres
    #
    chash
    cfv
    #
    @4
    cdm
    #
    chash
    cfv
    #
    cB
    chash
    cfv
    @3
    @4
    wfun
    #
    @5
    @7
    wceq
    #
    @0
    @1
    @8
    @2
    cB
    cA
    funres
    3ad2ant1
    @3
    @4
    cfn
    wcel
    #
    @8
    @9
    wb
    @1
    @0
    @10
    @2
    cB
    cA
    finresfin
    3ad2ant2
    @4
    hashfun
    syl
    mpbid
    @3
    @6
    cB
    chash
    @2
    @0
    @6
    cB
    wceq
    #
    @1
    @2
    @11
    cB
    cA
    ssdmres
    biimpi
    3ad2ant3
    fveq2d
    eqtrd
end
