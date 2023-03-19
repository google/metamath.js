include "wcel.mm"
include "wiso.mm"
include "w3a.mm"
include "cordt.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "ccnv.mm"
include "chmeo.mm"
include "ordthmeolem.mm"
include "isocnv.mm"
include "3com12.mm"
include "syl3an3.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem ordthmeo
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ordthmeo.1: |- X = dom R
  assume ordthmeo.2: |- Y = dom S


  assert |- ( ( R e. V /\ S e. W /\ F Isom R , S ( X , Y ) ) -> F e. ( ( ordTop ` R ) Homeo ( ordTop ` S ) ) )

  proof
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    cX
    cY
    cR
    cS
    cF
    wiso
    #
    w3a
    cF
    cR
    cordt
    cfv
    #
    cS
    cordt
    cfv
    #
    ccn
    co
    wcel
    cF
    ccnv
    #
    @4
    @3
    ccn
    co
    wcel
    #
    cF
    @3
    @4
    chmeo
    co
    wcel
    cR
    cS
    cF
    cV
    cW
    cX
    cY
    ordthmeo.1
    ordthmeo.2
    ordthmeolem
    @2
    @0
    @1
    cY
    cX
    cS
    cR
    @5
    wiso
    #
    @6
    cX
    cY
    cR
    cS
    cF
    isocnv
    @1
    @0
    @7
    @6
    cS
    cR
    @5
    cW
    cV
    cY
    cX
    ordthmeo.2
    ordthmeo.1
    ordthmeolem
    3com12
    syl3an3
    cF
    @3
    @4
    ishmeo
    sylanbrc
end
