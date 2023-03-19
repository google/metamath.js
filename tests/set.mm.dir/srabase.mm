include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "1lt5.mm"
include "orci.mm"
include "sralem.mm"

theorem srabase
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( Base ` W ) = ( Base ` A ) )

  proof
    wph
    cA
    cS
    cbs
    c1
    cW
    srapart.a
    srapart.s
    df-base
    1nn
    c1
    c5
    clt
    wbr
    c8
    c1
    clt
    wbr
    1lt5
    orci
    sralem
end
