include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "2lt5.mm"
include "orci.mm"
include "sralem.mm"

theorem sraaddg
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( +g ` W ) = ( +g ` A ) )

  proof
    wph
    cA
    cS
    cplusg
    c2
    cW
    srapart.a
    srapart.s
    df-plusg
    2nn
    c2
    c5
    clt
    wbr
    c8
    c2
    clt
    wbr
    2lt5
    orci
    sralem
end
