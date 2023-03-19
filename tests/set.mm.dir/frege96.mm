include "wbr.mm"
include "ctcl.mm"
include "cfv.mm"
include "wi.mm"
include "frege95.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege96
  let cA: class A
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume frege95.x: |- X e. U
  assume frege95.y: |- Y e. V
  assume frege95.z: |- Z e. W
  assume frege95.r: |- R e. A


  assert |- ( X ( t+ ` R ) Y -> ( Y R Z -> X ( t+ ` R ) Z ) )

  proof
    cY
    cZ
    cR
    wbr
    #
    cX
    cY
    cR
    ctcl
    cfv
    #
    wbr
    #
    cX
    cZ
    @1
    wbr
    #
    wi
    wi
    @2
    @0
    @3
    wi
    wi
    cA
    cR
    cU
    cV
    cW
    cX
    cY
    cZ
    frege95.x
    frege95.y
    frege95.z
    frege95.r
    frege95
    @0
    @2
    @3
    ax-frege8
    ax-mp
end
