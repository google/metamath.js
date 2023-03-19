include "czrh.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "cfzo.mm"
include "co.mm"
include "cif.mm"
include "cres.mm"
include "cple.mm"
include "cbs.mm"
include "eqid.mm"
include "zntoslem.mm"

theorem zntos
  let cN: class N
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zntos.y: |- Y = ( Z/nZ ` N )


  assert |- ( N e. NN0 -> Y e. Toset )

  proof
    cY
    czrh
    cfv
    cN
    cc0
    wceq
    cz
    cc0
    cN
    cfzo
    co
    cif
    #
    cres
    #
    cY
    cple
    cfv
    #
    cN
    @0
    cY
    cbs
    cfv
    #
    cY
    zntos.y
    @1
    eqid
    @0
    eqid
    @2
    eqid
    @3
    eqid
    zntoslem
end
