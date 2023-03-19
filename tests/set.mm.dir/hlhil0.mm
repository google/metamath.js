include "c0g.mm"
include "cfv.mm"
include "cbs.mm"
include "eqidd.mm"
include "eqid.mm"
include "hlhilbase.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "hlhilplus.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "syl5eq.mm"

theorem hlhil0
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cV: class V
  let cX: class X
  assume hlhil0.h: |- H = ( LHyp ` K )
  assume hlhil0.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhil0.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhil0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhil0.z: |- .0. = ( 0g ` L )


  assert |- ( ph -> .0. = ( 0g ` U ) )

  proof
    wph
    c.0
    cL
    c0g
    cfv
    cU
    c0g
    cfv
    hlhil0.z
    wph
    vx
    vy
    cL
    cbs
    cfv
    #
    cL
    cU
    wph
    @0
    eqidd
    wph
    cU
    cH
    cK
    cL
    @0
    cW
    hlhil0.h
    hlhil0.u
    hlhil0.k
    hlhil0.l
    @0
    eqid
    hlhilbase
    wph
    vx
    cv
    @0
    wcel
    vy
    cv
    @0
    wcel
    wa
    vx
    vy
    cL
    cplusg
    cfv
    #
    cU
    cplusg
    cfv
    wph
    @1
    cU
    cH
    cK
    cL
    cW
    hlhil0.h
    hlhil0.u
    hlhil0.k
    hlhil0.l
    @1
    eqid
    hlhilplus
    oveqdr
    grpidpropd
    syl5eq
end
