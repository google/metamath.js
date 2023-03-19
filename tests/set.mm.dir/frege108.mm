include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wi.mm"
include "frege102.mm"
include "frege107.mm"
include "ax-mp.mm"

theorem frege108
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cV: class V
  let cY: class Y
  let cZ: class Z
  assume frege108.z: |- Z e. A
  assume frege108.y: |- Y e. B
  assume frege108.v: |- V e. C
  assume frege108.r: |- R e. D


  assert |- ( Z ( ( t+ ` R ) u. _I ) Y -> ( Y R V -> Z ( ( t+ ` R ) u. _I ) V ) )

  proof
    cZ
    cY
    cR
    ctcl
    cfv
    #
    cid
    cun
    #
    wbr
    #
    cY
    cV
    cR
    wbr
    #
    cZ
    cV
    @0
    wbr
    wi
    wi
    @2
    @3
    cZ
    cV
    @1
    wbr
    wi
    wi
    cA
    cB
    cC
    cD
    cR
    cV
    cZ
    cY
    frege108.z
    frege108.y
    frege108.v
    frege108.r
    frege102
    cC
    cR
    cV
    cY
    cZ
    frege108.v
    frege107
    ax-mp
end
