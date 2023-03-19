include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "cafv.mm"
include "cab.mm"
include "cuni.mm"
include "wceq.mm"
include "cop.mm"
include "df-br.mm"
include "eubii.mm"
include "eu2ndop1stv.mm"
include "sylbi.mm"
include "wa.mm"
include "cdm.mm"
include "wex.mm"
include "euex.mm"
include "eldmg.mm"
include "syl5ibrcom.mm"
include "impcom.mm"
include "wi.mm"
include "wdfat.mm"
include "dfdfat2.mm"
include "cfv.mm"
include "afvfundmfveq.mm"
include "fveu.mm"
include "sylan9eq.mm"
include "ex.mm"
include "sylbir.mm"
include "expcom.mm"
include "pm2.43a.mm"
include "adantl.mm"
include "mpd.mm"
include "mpancom.mm"

theorem afveu
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k

  disjoint A x
  disjoint F x
  disjoint k x
  assert |- ( E! x A F x -> ( F ''' A ) = U. { x | A F x } )

  proof
    cA
    cvv
    wcel
    #
    cA
    vx
    cv
    #
    cF
    wbr
    #
    vx
    weu
    #
    cA
    cF
    cafv
    #
    @2
    vx
    cab
    cuni
    #
    wceq
    #
    @3
    cA
    @1
    cop
    cF
    wcel
    #
    vx
    weu
    @0
    @2
    @7
    vx
    cA
    @1
    cF
    df-br
    eubii
    vx
    cA
    cF
    eu2ndop1stv
    sylbi
    @0
    @3
    wa
    cA
    cF
    cdm
    wcel
    #
    @6
    @3
    @0
    @8
    @3
    @8
    @0
    @2
    vx
    wex
    @2
    vx
    euex
    vx
    cA
    cF
    cvv
    eldmg
    syl5ibrcom
    impcom
    @3
    @8
    @6
    wi
    @0
    @8
    @3
    @6
    @8
    @3
    @3
    @6
    wi
    #
    @8
    @3
    wa
    cA
    cF
    wdfat
    #
    @9
    vx
    cA
    cF
    dfdfat2
    @10
    @3
    @6
    @10
    @3
    @4
    cA
    cF
    cfv
    @5
    cA
    cF
    afvfundmfveq
    vx
    cA
    cF
    fveu
    sylan9eq
    ex
    sylbir
    expcom
    pm2.43a
    adantl
    mpd
    mpancom
end
