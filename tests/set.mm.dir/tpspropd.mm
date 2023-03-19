include "ctopn.mm"
include "cfv.mm"
include "cbs.mm"
include "ctopon.mm"
include "wcel.mm"
include "ctps.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "eqid.mm"
include "istps.mm"
include "3bitr4g.mm"

theorem tpspropd
  let wph: wff ph
  let cK: class K
  let cL: class L
  assume tpspropd.1: |- ( ph -> ( Base ` K ) = ( Base ` L ) )
  assume tpspropd.2: |- ( ph -> ( TopOpen ` K ) = ( TopOpen ` L ) )


  assert |- ( ph -> ( K e. TopSp <-> L e. TopSp ) )

  proof
    wph
    cK
    ctopn
    cfv
    #
    cK
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    cL
    ctopn
    cfv
    #
    cL
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    cK
    ctps
    wcel
    cL
    ctps
    wcel
    wph
    @0
    @3
    @2
    @5
    tpspropd.2
    wph
    @1
    @4
    ctopon
    tpspropd.1
    fveq2d
    eleq12d
    @1
    @0
    cK
    @1
    eqid
    @0
    eqid
    istps
    @4
    @3
    cL
    @4
    eqid
    @3
    eqid
    istps
    3bitr4g
end
