include "c0g.mm"
include "cfv.mm"
include "cbs.mm"
include "eqidd.mm"
include "eqid.mm"
include "hlhilsbase2.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "hlhilsplus2.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "syl5eq.mm"

theorem hlhils0
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume hlhilsbase.h: |- H = ( LHyp ` K )
  assume hlhilsbase.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilsbase.s: |- S = ( Scalar ` L )
  assume hlhilsbase.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilsbase.r: |- R = ( Scalar ` U )
  assume hlhilsbase.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhils0.z: |- .0. = ( 0g ` S )


  assert |- ( ph -> .0. = ( 0g ` R ) )

  proof
    wph
    c.0
    cS
    c0g
    cfv
    cR
    c0g
    cfv
    hlhils0.z
    wph
    vx
    vy
    cS
    cbs
    cfv
    #
    cS
    cR
    wph
    @0
    eqidd
    wph
    @0
    cR
    cS
    cU
    cH
    cK
    cL
    cW
    hlhilsbase.h
    hlhilsbase.l
    hlhilsbase.s
    hlhilsbase.u
    hlhilsbase.r
    hlhilsbase.k
    @0
    eqid
    hlhilsbase2
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
    cS
    cplusg
    cfv
    #
    cR
    cplusg
    cfv
    wph
    @1
    cR
    cS
    cU
    cH
    cK
    cL
    cW
    hlhilsbase.h
    hlhilsbase.l
    hlhilsbase.s
    hlhilsbase.u
    hlhilsbase.r
    hlhilsbase.k
    @1
    eqid
    hlhilsplus2
    oveqdr
    grpidpropd
    syl5eq
end
