include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cip.mm"
include "eqid.mm"
include "hlhilip.mm"
include "syl6reqr.mm"
include "oveqd.mm"
include "wcel.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fvex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem hlhilipval
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let c.xi: class .,
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume hlhilip.h: |- H = ( LHyp ` K )
  assume hlhilip.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilip.v: |- V = ( Base ` L )
  assume hlhilip.s: |- S = ( ( HDMap ` K ) ` W )
  assume hlhilip.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilip.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilip.i: |- ., = ( .i ` U )
  assume hlhilip.x: |- ( ph -> X e. V )
  assume hlhilip.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( X ., Y ) = ( ( S ` Y ) ` X ) )

  proof
    wph
    cX
    cY
    c.xi
    co
    cX
    cY
    vx
    vy
    cV
    cV
    vx
    cv
    #
    vy
    cv
    #
    cS
    cfv
    #
    cfv
    #
    cmpt2
    #
    co
    #
    cX
    cY
    cS
    cfv
    #
    cfv
    #
    wph
    c.xi
    @4
    cX
    cY
    wph
    @4
    cU
    cip
    cfv
    c.xi
    wph
    vx
    vy
    cS
    cU
    cH
    @4
    cK
    cL
    cV
    cW
    hlhilip.h
    hlhilip.l
    hlhilip.v
    hlhilip.s
    hlhilip.u
    hlhilip.k
    @4
    eqid
    #
    hlhilip
    hlhilip.i
    syl6reqr
    oveqd
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    @5
    @7
    wceq
    hlhilip.x
    hlhilip.y
    vx
    vy
    cX
    cY
    cV
    cV
    @3
    @7
    @4
    cX
    @2
    cfv
    @0
    cX
    @2
    fveq2
    @1
    cY
    wceq
    cX
    @2
    @6
    @1
    cY
    cS
    fveq2
    fveq1d
    @8
    cX
    @6
    fvex
    ovmpt2
    syl2anc
    eqtrd
end
