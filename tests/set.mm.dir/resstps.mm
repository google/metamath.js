include "ctps.mm"
include "wcel.mm"
include "wa.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cress.mm"
include "cbs.mm"
include "ctopon.mm"
include "cin.mm"
include "eqid.mm"
include "istps.mm"
include "resttopon2.mm"
include "sylanb.mm"
include "wceq.mm"
include "ressbas.mm"
include "adantl.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "resstopn.mm"
include "sylibr.mm"

theorem resstps
  let cA: class A
  let cK: class K
  let cV: class V


  assert |- ( ( K e. TopSp /\ A e. V ) -> ( K |`s A ) e. TopSp )

  proof
    cK
    ctps
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cK
    ctopn
    cfv
    #
    cA
    crest
    co
    #
    cK
    cA
    cress
    co
    #
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    @5
    ctps
    wcel
    @2
    @4
    cA
    cK
    cbs
    cfv
    #
    cin
    #
    ctopon
    cfv
    #
    @7
    @0
    @3
    @8
    ctopon
    cfv
    wcel
    @1
    @4
    @10
    wcel
    @8
    @3
    cK
    @8
    eqid
    #
    @3
    eqid
    #
    istps
    cA
    @3
    cV
    @8
    resttopon2
    sylanb
    @2
    @9
    @6
    ctopon
    @1
    @9
    @6
    wceq
    @0
    cA
    @8
    @5
    cV
    cK
    @5
    eqid
    #
    @11
    ressbas
    adantl
    fveq2d
    eleqtrd
    @6
    @4
    @5
    @6
    eqid
    cA
    @5
    @3
    cK
    @13
    @12
    resstopn
    istps
    sylibr
end
