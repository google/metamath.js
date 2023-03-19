include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "weu.mm"
include "cvv.mm"
include "euex.mm"
include "wi.mm"
include "nfeu1.mm"
include "nfcv.mm"
include "nfel1.mm"
include "nfim.mm"
include "wn.mm"
include "wa.mm"
include "c0.mm"
include "opprc1.mm"
include "eleq1d.mm"
include "wal.mm"
include "ax-5.mm"
include "alneu.mm"
include "syl.mm"
include "syl6bi.mm"
include "impcom.mm"
include "wb.mm"
include "eubidv.mm"
include "notbid.mm"
include "adantl.mm"
include "mpbird.mm"
include "ex.mm"
include "con4d.mm"
include "exlimi.mm"
include "mpcom.mm"

theorem eu2ndop1stv
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vk: setvar k
  let vx: setvar x

  disjoint A y
  disjoint V y
  disjoint k x
  assert |- ( E! y <. A , y >. e. V -> A e. _V )

  proof
    cA
    vy
    cv
    #
    cop
    #
    cV
    wcel
    #
    vy
    wex
    @2
    vy
    weu
    #
    cA
    cvv
    wcel
    #
    @2
    vy
    euex
    @2
    @3
    @4
    wi
    vy
    @3
    @4
    vy
    @2
    vy
    nfeu1
    vy
    cA
    cvv
    vy
    cA
    nfcv
    nfel1
    nfim
    @2
    @4
    @3
    @2
    @4
    wn
    #
    @3
    wn
    #
    @2
    @5
    wa
    @6
    c0
    cV
    wcel
    #
    vy
    weu
    #
    wn
    #
    @5
    @2
    @9
    @5
    @2
    @7
    @9
    @5
    @1
    c0
    cV
    cA
    @0
    opprc1
    eleq1d
    #
    @7
    @7
    vy
    wal
    @9
    @7
    vy
    ax-5
    @7
    vy
    alneu
    syl
    syl6bi
    impcom
    @5
    @6
    @9
    wb
    @2
    @5
    @3
    @8
    @5
    @2
    @7
    vy
    @10
    eubidv
    notbid
    adantl
    mpbird
    ex
    con4d
    exlimi
    mpcom
end
