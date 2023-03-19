include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "1lt4.mm"
include "hlhilslem.mm"

theorem hlhilsbase
  let wph: wff ph
  let cC: class C
  let cR: class R
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
  assume hlhilsbase.c: |- C = ( Base ` E )


  assert |- ( ph -> C = ( Base ` R ) )

  proof
    wph
    cC
    cR
    cU
    cE
    cbs
    cH
    cK
    c1
    cW
    hlhilslem.h
    hlhilslem.e
    hlhilslem.u
    hlhilslem.r
    hlhilslem.k
    df-base
    1nn
    1lt4
    hlhilsbase.c
    hlhilslem
end
