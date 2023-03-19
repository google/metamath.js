include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "csn.mm"
include "cima.mm"
include "whe.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "frege109.mm"
include "wcel.mm"
include "cvv.mm"
include "imaundir.mm"
include "fvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "imai.mm"
include "snex.mm"
include "eqeltri.mm"
include "unex.mm"
include "frege78.mm"
include "cop.mm"
include "elexi.mm"
include "vex.mm"
include "elimasn.mm"
include "df-br.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "albii.mm"
include "3imtr3g.mm"

theorem frege110
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cM: class M
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege110.x: |- X e. A
  assume frege110.y: |- Y e. B
  assume frege110.m: |- M e. C
  assume frege110.r: |- R e. D

  disjoint R a
  disjoint X a
  disjoint Y a
  assert |- ( A. a ( Y R a -> X ( ( t+ ` R ) u. _I ) a ) -> ( Y ( t+ ` R ) M -> X ( ( t+ ` R ) u. _I ) M ) )

  proof
    cR
    ctcl
    cfv
    #
    cid
    cun
    #
    cX
    csn
    #
    cima
    #
    cR
    whe
    #
    cY
    va
    cv
    #
    cR
    wbr
    #
    cX
    @5
    @1
    wbr
    #
    wi
    #
    va
    wal
    #
    cY
    cM
    @0
    wbr
    #
    cX
    cM
    @1
    wbr
    #
    wi
    #
    wi
    cR
    cA
    cD
    cX
    frege110.x
    frege110.r
    frege109
    @4
    @6
    @5
    @3
    wcel
    #
    wi
    #
    va
    wal
    @10
    cM
    @3
    wcel
    #
    wi
    @9
    @12
    @3
    cvv
    cR
    cB
    cC
    cD
    cY
    cM
    va
    frege110.y
    frege110.m
    frege110.r
    @3
    @0
    @2
    cima
    #
    cid
    @2
    cima
    #
    cun
    cvv
    @0
    cid
    @2
    imaundir
    @16
    @17
    @0
    cvv
    wcel
    @16
    cvv
    wcel
    cR
    ctcl
    fvex
    @0
    @2
    cvv
    imaexg
    ax-mp
    @17
    @2
    cvv
    @2
    imai
    cX
    snex
    eqeltri
    unex
    eqeltri
    frege78
    @14
    @8
    va
    @13
    @7
    @6
    @13
    cX
    @5
    cop
    @1
    wcel
    @7
    @1
    cX
    @5
    cX
    cA
    frege110.x
    elexi
    #
    va
    vex
    elimasn
    cX
    @5
    @1
    df-br
    bitr4i
    imbi2i
    albii
    @15
    @11
    @10
    @15
    cX
    cM
    cop
    @1
    wcel
    @11
    @1
    cX
    cM
    @18
    cM
    cC
    frege110.m
    elexi
    elimasn
    cX
    cM
    @1
    df-br
    bitr4i
    imbi2i
    3imtr3g
    ax-mp
end
