include "cds.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "df-ds.mm"
include "1nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "c8.mm"
include "clt.mm"
include "wbr.mm"
include "c5.mm"
include "1nn.mm"
include "2nn0.mm"
include "8nn0.mm"
include "8lt10.mm"
include "declti.mm"
include "olci.mm"
include "sralem.mm"

theorem srads
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( dist ` W ) = ( dist ` A ) )

  proof
    wph
    cA
    cS
    cds
    c1
    c2
    cdc
    #
    cW
    srapart.a
    srapart.s
    df-ds
    c1
    c2
    1nn0
    2nn
    decnncl
    c8
    @0
    clt
    wbr
    @0
    c5
    clt
    wbr
    c1
    c2
    c8
    1nn
    2nn0
    8nn0
    8lt10
    declti
    olci
    sralem
end
