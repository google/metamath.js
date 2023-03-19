include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "eqid.mm"
include "eldifad.mm"
include "snssd.mm"
include "dochocsp.mm"
include "clsa.mm"
include "dvhlmod.mm"
include "lsatlspsn.mm"
include "dochsatshp.mm"
include "eqeltrrd.mm"

theorem dochsnshp
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume dochsnshp.h: |- H = ( LHyp ` K )
  assume dochsnshp.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsnshp.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsnshp.v: |- V = ( Base ` U )
  assume dochsnshp.z: |- .0. = ( 0g ` U )
  assume dochsnshp.y: |- Y = ( LSHyp ` U )
  assume dochsnshp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsnshp.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( ._|_ ` { X } ) e. Y )

  proof
    wph
    cX
    csn
    #
    cU
    clspn
    cfv
    #
    cfv
    #
    c.pe
    cfv
    @0
    c.pe
    cfv
    cY
    wph
    cU
    cH
    cK
    @1
    c.pe
    cV
    cW
    @0
    dochsnshp.h
    dochsnshp.u
    dochsnshp.o
    dochsnshp.v
    @1
    eqid
    #
    dochsnshp.k
    wph
    cX
    cV
    wph
    cX
    cV
    c.0
    csn
    dochsnshp.x
    eldifad
    snssd
    dochocsp
    wph
    cU
    clsa
    cfv
    #
    @2
    cU
    cH
    cK
    c.pe
    cW
    cY
    dochsnshp.h
    dochsnshp.u
    dochsnshp.o
    @4
    eqid
    #
    dochsnshp.y
    dochsnshp.k
    wph
    @4
    @1
    cV
    cU
    cX
    c.0
    dochsnshp.v
    @3
    dochsnshp.z
    @5
    wph
    cU
    cH
    cK
    cW
    dochsnshp.h
    dochsnshp.u
    dochsnshp.k
    dvhlmod
    dochsnshp.x
    lsatlspsn
    dochsatshp
    eqeltrrd
end
