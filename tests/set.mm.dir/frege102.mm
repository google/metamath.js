include "wceq.mm"
include "wbr.mm"
include "ctcl.mm"
include "cfv.mm"
include "wi.mm"
include "cid.mm"
include "cun.mm"
include "frege92.mm"
include "frege96.mm"
include "frege101.mm"
include "mp2.mm"

theorem frege102
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume frege102.x: |- X e. A
  assume frege102.z: |- Z e. B
  assume frege102.v: |- V e. C
  assume frege102.r: |- R e. D


  assert |- ( X ( ( t+ ` R ) u. _I ) Z -> ( Z R V -> X ( t+ ` R ) V ) )

  proof
    cZ
    cX
    wceq
    cZ
    cV
    cR
    wbr
    cX
    cV
    cR
    ctcl
    cfv
    #
    wbr
    wi
    #
    wi
    cX
    cZ
    @0
    wbr
    @1
    wi
    cX
    cZ
    @0
    cid
    cun
    wbr
    @1
    wi
    cR
    cB
    cC
    cD
    cZ
    cV
    cX
    frege102.z
    frege102.v
    frege102.r
    frege92
    cD
    cR
    cA
    cB
    cC
    cX
    cZ
    cV
    frege102.x
    frege102.z
    frege102.v
    frege102.r
    frege96
    cR
    cB
    cV
    cX
    cZ
    frege102.z
    frege101
    mp2
end
