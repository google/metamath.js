include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "csn.mm"
include "eqid.mm"
include "doch1.mm"
include "fveq2d.mm"
include "doch0.mm"
include "eqtrd.mm"
include "syl.mm"

theorem dochoc1
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume dochoc1.h: |- H = ( LHyp ` K )
  assume dochoc1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochoc1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochoc1.v: |- V = ( Base ` U )
  assume dochoc1.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` V ) ) = V )

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
    cV
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cV
    wceq
    dochoc1.k
    @0
    @2
    cU
    c0g
    cfv
    #
    csn
    #
    c.pe
    cfv
    cV
    @0
    @1
    @4
    c.pe
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    dochoc1.h
    dochoc1.u
    dochoc1.o
    dochoc1.v
    @3
    eqid
    #
    doch1
    fveq2d
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    dochoc1.h
    dochoc1.u
    dochoc1.o
    dochoc1.v
    @5
    doch0
    eqtrd
    syl
end
