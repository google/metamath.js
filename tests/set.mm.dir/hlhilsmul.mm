include "cmulr.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "3lt4.mm"
include "hlhilslem.mm"

theorem hlhilsmul
  let wph: wff ph
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cH: class H
  let cK: class K
  let cW: class W
  assume hlhilslem.h: |- H = ( LHyp ` K )
  assume hlhilslem.e: |- E = ( ( EDRing ` K ) ` W )
  assume hlhilslem.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilslem.r: |- R = ( Scalar ` U )
  assume hlhilslem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilsmul.m: |- .x. = ( .r ` E )


  assert |- ( ph -> .x. = ( .r ` R ) )

  proof
    wph
    c.x
    cR
    cU
    cE
    cmulr
    cH
    cK
    c3
    cW
    hlhilslem.h
    hlhilslem.e
    hlhilslem.u
    hlhilslem.r
    hlhilslem.k
    df-mulr
    3nn
    3lt4
    hlhilsmul.m
    hlhilslem
end
