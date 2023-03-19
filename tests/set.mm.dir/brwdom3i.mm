include "cwdom.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "relwdom.mm"
include "brrelexi.mm"
include "brrelex2i.mm"
include "brwdom3.mm"
include "syl2anc.mm"
include "ibi.mm"

theorem brwdom3i
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z

  disjoint X f
  disjoint X x
  disjoint X y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint X w
  disjoint X z
  disjoint f w
  disjoint f z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint Y w
  disjoint Y z
  assert |- ( X ~<_* Y -> E. f A. x e. X E. y e. Y x = ( f ` y ) )

  proof
    cX
    cY
    cwdom
    wbr
    #
    vx
    cv
    vy
    cv
    vf
    cv
    cfv
    wceq
    vy
    cY
    wrex
    vx
    cX
    wral
    vf
    wex
    #
    @0
    cX
    cvv
    wcel
    cY
    cvv
    wcel
    @0
    @1
    wb
    cX
    cY
    cwdom
    relwdom
    brrelexi
    cX
    cY
    cwdom
    relwdom
    brrelex2i
    vx
    vy
    vf
    cvv
    cvv
    cX
    cY
    brwdom3
    syl2anc
    ibi
end
