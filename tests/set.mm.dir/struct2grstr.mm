include "cnx.mm"
include "cedgf.mm"
include "cfv.mm"
include "baseltedgf.mm"
include "edgfndxnn.mm"
include "2strstr1.mm"

theorem struct2grstr
  let cE: class E
  let cG: class G
  let cV: class V
  assume struct2grvtx.g: |- G = { <. ( Base ` ndx ) , V >. , <. ( .ef ` ndx ) , E >. }


  assert |- G Struct <. ( Base ` ndx ) , ( .ef ` ndx ) >.

  proof
    cV
    cE
    cG
    cnx
    cedgf
    cfv
    struct2grvtx.g
    baseltedgf
    edgfndxnn
    2strstr1
end
