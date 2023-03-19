include "cts.mm"
include "c9.mm"
include "df-tset.mm"
include "9nn.mm"
include "c8.mm"
include "clt.mm"
include "wbr.mm"
include "c5.mm"
include "8lt9.mm"
include "olci.mm"
include "sralem.mm"

theorem sratset
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( TopSet ` W ) = ( TopSet ` A ) )

  proof
    wph
    cA
    cS
    cts
    c9
    cW
    srapart.a
    srapart.s
    df-tset
    9nn
    c8
    c9
    clt
    wbr
    c9
    c5
    clt
    wbr
    8lt9
    olci
    sralem
end
