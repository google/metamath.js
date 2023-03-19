include "cmulr.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "3lt5.mm"
include "orci.mm"
include "sralem.mm"

theorem sramulr
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( .r ` W ) = ( .r ` A ) )

  proof
    wph
    cA
    cS
    cmulr
    c3
    cW
    srapart.a
    srapart.s
    df-mulr
    3nn
    c3
    c5
    clt
    wbr
    c8
    c3
    clt
    wbr
    3lt5
    orci
    sralem
end
