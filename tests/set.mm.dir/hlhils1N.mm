include "cur.mm"
include "cfv.mm"
include "cbs.mm"
include "eqidd.mm"
include "eqid.mm"
include "hlhilsbase2.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "hlhilsmul2.mm"
include "oveqdr.mm"
include "rngidpropd.mm"
include "syl5eq.mm"

theorem hlhils1N
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hlhilsbase.h: |- H = ( LHyp ` K )
  assume hlhilsbase.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilsbase.s: |- S = ( Scalar ` L )
  assume hlhilsbase.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilsbase.r: |- R = ( Scalar ` U )
  assume hlhilsbase.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhils1.t: |- .1. = ( 1r ` S )


  assert |- ( ph -> .1. = ( 1r ` R ) )

  proof
    wph
    c.1
    cS
    cur
    cfv
    cR
    cur
    cfv
    hlhils1.t
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
    cmulr
    cfv
    #
    cR
    cmulr
    cfv
    wph
    cR
    cS
    @1
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
    hlhilsmul2
    oveqdr
    rngidpropd
    syl5eq
end
