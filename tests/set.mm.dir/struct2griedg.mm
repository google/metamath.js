include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cedgf.mm"
include "cop.mm"
include "cstr.mm"
include "wbr.mm"
include "struct2grstr.mm"
include "a1i.mm"
include "simpl.mm"
include "simpr.mm"
include "cpr.mm"
include "wss.mm"
include "eqimss2i.mm"
include "structgrssiedg.mm"

theorem struct2griedg
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  assume struct2grvtx.g: |- G = { <. ( Base ` ndx ) , V >. , <. ( .ef ` ndx ) , E >. }


  assert |- ( ( V e. X /\ E e. Y ) -> ( iEdg ` G ) = E )

  proof
    cV
    cX
    wcel
    #
    cE
    cY
    wcel
    #
    wa
    #
    cE
    cG
    cV
    cnx
    cbs
    cfv
    #
    cnx
    cedgf
    cfv
    #
    cop
    #
    cX
    cY
    cG
    @5
    cstr
    wbr
    @2
    cE
    cG
    cV
    struct2grvtx.g
    struct2grstr
    a1i
    @0
    @1
    simpl
    @0
    @1
    simpr
    @3
    cV
    cop
    @4
    cE
    cop
    cpr
    #
    cG
    wss
    @2
    cG
    @6
    struct2grvtx.g
    eqimss2i
    a1i
    structgrssiedg
end
