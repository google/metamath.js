include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "2lt4.mm"
include "hlhilslem.mm"

theorem hlhilsplus
  let wph: wff ph
  let c.pl: class .+
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
  assume hlhilsplus.a: |- .+ = ( +g ` E )


  assert |- ( ph -> .+ = ( +g ` R ) )

  proof
    wph
    c.pl
    cR
    cU
    cE
    cplusg
    cH
    cK
    c2
    cW
    hlhilslem.h
    hlhilslem.e
    hlhilslem.u
    hlhilslem.r
    hlhilslem.k
    df-plusg
    2nn
    2lt4
    hlhilsplus.a
    hlhilslem
end
