include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cid.mm"
include "cun.mm"
include "wi.mm"
include "frege106.mm"
include "frege7.mm"
include "ax-mp.mm"

theorem frege107
  let cA: class A
  let cR: class R
  let cV: class V
  let cY: class Y
  let cZ: class Z
  assume frege107.v: |- V e. A


  assert |- ( ( Z ( ( t+ ` R ) u. _I ) Y -> ( Y R V -> Z ( t+ ` R ) V ) ) -> ( Z ( ( t+ ` R ) u. _I ) Y -> ( Y R V -> Z ( ( t+ ` R ) u. _I ) V ) ) )

  proof
    cZ
    cV
    cR
    ctcl
    cfv
    #
    wbr
    #
    cZ
    cV
    @0
    cid
    cun
    #
    wbr
    #
    wi
    cZ
    cY
    @2
    wbr
    #
    cY
    cV
    cR
    wbr
    #
    @1
    wi
    wi
    @4
    @5
    @3
    wi
    wi
    wi
    cR
    cA
    cZ
    cV
    frege107.v
    frege106
    @1
    @3
    @4
    @5
    frege7
    ax-mp
end
