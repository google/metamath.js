include "wcel.mm"
include "cple.mm"
include "cfv.mm"
include "cid.mm"
include "cdif.mm"
include "cplt.mm"
include "eqid.mm"
include "pltfval.mm"
include "cvv.mm"
include "wceq.mm"
include "coppg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "oppgle.mm"
include "ax-mp.mm"
include "syl6eqr.mm"

theorem oppglt
  let cR: class R
  let c.lt: class .<
  let cO: class O
  let cV: class V
  assume oppglt.1: |- O = ( oppG ` R )
  assume oppglt.2: |- .< = ( lt ` R )


  assert |- ( R e. V -> .< = ( lt ` O ) )

  proof
    cR
    cV
    wcel
    c.lt
    cR
    cple
    cfv
    #
    cid
    cdif
    #
    cO
    cplt
    cfv
    #
    cV
    c.lt
    cR
    @0
    @0
    eqid
    #
    oppglt.2
    pltfval
    cO
    cvv
    wcel
    @2
    @1
    wceq
    cO
    cR
    coppg
    cfv
    cvv
    oppglt.1
    cR
    coppg
    fvex
    eqeltri
    cvv
    @2
    cO
    @0
    cR
    @0
    cO
    oppglt.1
    @3
    oppgle
    @2
    eqid
    pltfval
    ax-mp
    syl6eqr
end
