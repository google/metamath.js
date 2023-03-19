include "cnx.mm"
include "cedgf.mm"
include "cfv.mm"
include "edgfndxnn.mm"
include "baseltedgf.mm"
include "structvtxval.mm"

theorem struct2grvtx
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  assume struct2grvtx.g: |- G = { <. ( Base ` ndx ) , V >. , <. ( .ef ` ndx ) , E >. }


  assert |- ( ( V e. X /\ E e. Y ) -> ( Vtx ` G ) = V )

  proof
    cnx
    cedgf
    cfv
    cE
    cG
    cV
    cX
    cY
    edgfndxnn
    baseltedgf
    struct2grvtx.g
    structvtxval
end
