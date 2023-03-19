include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "doch0.mm"
include "fveq2d.mm"
include "doch1.mm"
include "eqtrd.mm"
include "syl.mm"

theorem dochoc0
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let c.0: class .0.
  assume dochoc0.h: |- H = ( LHyp ` K )
  assume dochoc0.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochoc0.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochoc0.z: |- .0. = ( 0g ` U )
  assume dochoc0.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` { .0. } ) ) = { .0. } )

  proof
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    c.0
    csn
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wceq
    dochoc0.k
    @0
    @3
    cU
    cbs
    cfv
    #
    c.pe
    cfv
    @1
    @0
    @2
    @4
    c.pe
    cU
    cH
    cK
    c.pe
    @4
    cW
    c.0
    dochoc0.h
    dochoc0.u
    dochoc0.o
    @4
    eqid
    #
    dochoc0.z
    doch0
    fveq2d
    cU
    cH
    cK
    c.pe
    @4
    cW
    c.0
    dochoc0.h
    dochoc0.u
    dochoc0.o
    @5
    dochoc0.z
    doch1
    eqtrd
    syl
end
