include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "wa.mm"
include "cvtx.mm"
include "cedg.mm"
include "wbr.mm"
include "cusgr.mm"
include "wi.mm"
include "ausgrusgri.mm"
include "3exp.mm"
include "com23.mm"
include "imp.mm"
include "usgrausgri.mm"
include "impbid1.mm"

theorem usgrausgrb
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cO: class O
  let cW: class W
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y
  assume ausgr.1: |- G = { <. v , e >. | e C_ { x e. ~P v | ( # ` x ) = 2 } }
  assume ausgrusgri.1: |- O = { f | f : dom f -1-1-> ran f }

  disjoint e v
  disjoint e x
  disjoint v x
  disjoint H e
  disjoint H v
  disjoint H x
  disjoint H f
  disjoint W x
  disjoint E e
  disjoint E v
  disjoint E x
  disjoint V e
  disjoint V v
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ( H e. W /\ ( iEdg ` H ) e. O ) -> ( ( Vtx ` H ) G ( Edg ` H ) <-> H e. USGraph ) )

  proof
    cH
    cW
    wcel
    #
    cH
    ciedg
    cfv
    cO
    wcel
    #
    wa
    cH
    cvtx
    cfv
    cH
    cedg
    cfv
    cG
    wbr
    #
    cH
    cusgr
    wcel
    #
    @0
    @1
    @2
    @3
    wi
    @0
    @2
    @1
    @3
    @0
    @2
    @1
    @3
    vx
    vv
    ve
    vf
    cG
    cH
    cO
    cW
    ausgr.1
    ausgrusgri.1
    ausgrusgri
    3exp
    com23
    imp
    vx
    vv
    ve
    cG
    cH
    ausgr.1
    usgrausgri
    impbid1
end
