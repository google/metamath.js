include "srabase.mm"
include "sratset.mm"
include "topnpropd.mm"

theorem sratopn
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( TopOpen ` W ) = ( TopOpen ` A ) )

  proof
    wph
    cW
    cA
    wph
    cA
    cS
    cW
    srapart.a
    srapart.s
    srabase
    wph
    cA
    cS
    cW
    srapart.a
    srapart.s
    sratset
    topnpropd
end
