include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cstr.mm"
include "wbr.mm"
include "2strstr1.mm"
include "a1i.mm"
include "structvtxvallem.mm"
include "simpl.mm"
include "cpr.mm"
include "opex.mm"
include "prid1.mm"
include "eleqtrri.mm"
include "basvtxval.mm"

theorem structvtxval
  let cS: class S
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  assume structvtxvallem.s: |- S e. NN
  assume structvtxvallem.b: |- ( Base ` ndx ) < S
  assume structvtxvallem.g: |- G = { <. ( Base ` ndx ) , V >. , <. S , E >. }


  assert |- ( ( V e. X /\ E e. Y ) -> ( Vtx ` G ) = V )

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
    cG
    cV
    cnx
    cbs
    cfv
    #
    cS
    cop
    #
    cX
    cG
    @4
    cstr
    wbr
    @2
    cV
    cE
    cG
    cS
    structvtxvallem.g
    structvtxvallem.b
    structvtxvallem.s
    2strstr1
    a1i
    cS
    cE
    cG
    cV
    cX
    cY
    structvtxvallem.s
    structvtxvallem.b
    structvtxvallem.g
    structvtxvallem
    @0
    @1
    simpl
    @3
    cV
    cop
    #
    cG
    wcel
    @2
    @5
    @5
    cS
    cE
    cop
    #
    cpr
    cG
    @5
    @6
    @3
    cV
    opex
    prid1
    structvtxvallem.g
    eleqtrri
    a1i
    basvtxval
end
