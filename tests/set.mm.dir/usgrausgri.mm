include "cusgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "wbr.mm"
include "usgredgss.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "isausgr.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem usgrausgri
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let cG: class G
  let cH: class H
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y
  assume ausgr.1: |- G = { <. v , e >. | e C_ { x e. ~P v | ( # ` x ) = 2 } }

  disjoint e v
  disjoint e x
  disjoint v x
  disjoint H e
  disjoint H v
  disjoint H x
  disjoint E e
  disjoint E v
  disjoint E x
  disjoint V e
  disjoint V v
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( H e. USGraph -> ( Vtx ` H ) G ( Edg ` H ) )

  proof
    cH
    cusgr
    wcel
    cH
    cedg
    cfv
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cH
    cvtx
    cfv
    #
    cpw
    crab
    wss
    #
    @1
    @0
    cG
    wbr
    #
    vx
    cH
    usgredgss
    @1
    cvv
    wcel
    @0
    cvv
    wcel
    @3
    @2
    wb
    cH
    cvtx
    fvex
    cH
    cedg
    fvex
    vx
    vv
    ve
    @0
    cG
    @1
    cvv
    cvv
    ausgr.1
    isausgr
    mp2an
    sylibr
end
