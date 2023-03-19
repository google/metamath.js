include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "cn.mm"
include "fvexd.mm"
include "a1i.mm"
include "simpl.mm"
include "simpr.mm"
include "cop.mm"
include "cpr.mm"
include "prex.mm"
include "eqeltri.mm"
include "wne.mm"
include "basendxnn.mm"
include "nnrei.mm"
include "ltneii.mm"
include "wss.mm"
include "eqimss2i.mm"
include "hashdmpropge2.mm"

theorem structvtxvallem
  let cS: class S
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  assume structvtxvallem.s: |- S e. NN
  assume structvtxvallem.b: |- ( Base ` ndx ) < S
  assume structvtxvallem.g: |- G = { <. ( Base ` ndx ) , V >. , <. S , E >. }


  assert |- ( ( V e. X /\ E e. Y ) -> 2 <_ ( # ` dom G ) )

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
    cnx
    cbs
    cfv
    #
    cS
    cV
    cE
    cG
    cvv
    cn
    cX
    cY
    cvv
    @2
    cnx
    cbs
    fvexd
    cS
    cn
    wcel
    @2
    structvtxvallem.s
    a1i
    @0
    @1
    simpl
    @0
    @1
    simpr
    cG
    cvv
    wcel
    @2
    cG
    @3
    cV
    cop
    #
    cS
    cE
    cop
    #
    cpr
    #
    cvv
    structvtxvallem.g
    @4
    @5
    prex
    eqeltri
    a1i
    @3
    cS
    wne
    @2
    @3
    cS
    @3
    basendxnn
    nnrei
    structvtxvallem.b
    ltneii
    a1i
    @6
    cG
    wss
    @2
    cG
    @6
    structvtxvallem.g
    eqimss2i
    a1i
    hashdmpropge2
end
