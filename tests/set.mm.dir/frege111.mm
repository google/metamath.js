include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wi.mm"
include "wn.mm"
include "frege108.mm"
include "frege25.mm"
include "ax-mp.mm"

theorem frege111
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cV: class V
  let cY: class Y
  let cZ: class Z
  assume frege111.z: |- Z e. A
  assume frege111.y: |- Y e. B
  assume frege111.v: |- V e. C
  assume frege111.r: |- R e. D


  assert |- ( Z ( ( t+ ` R ) u. _I ) Y -> ( Y R V -> ( -. V ( t+ ` R ) Z -> Z ( ( t+ ` R ) u. _I ) V ) ) )

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
    @1
    wbr
    #
    wi
    wi
    @2
    @3
    cV
    cZ
    @0
    wbr
    wn
    #
    @4
    wi
    wi
    wi
    cA
    cB
    cC
    cD
    cR
    cV
    cY
    cZ
    frege111.z
    frege111.y
    frege111.v
    frege111.r
    frege108
    @2
    @3
    @4
    @5
    frege25
    ax-mp
end
