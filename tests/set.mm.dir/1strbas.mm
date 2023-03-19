include "cbs.mm"
include "c1.mm"
include "cop.mm"
include "1strstr.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "csn.mm"
include "eqimss2i.mm"
include "strfv.mm"

theorem 1strbas
  let cB: class B
  let cG: class G
  let cV: class V
  assume 1str.g: |- G = { <. ( Base ` ndx ) , B >. }


  assert |- ( B e. V -> B = ( Base ` G ) )

  proof
    cB
    cG
    cbs
    cV
    c1
    c1
    cop
    cB
    cG
    1str.g
    1strstr
    baseid
    cG
    cnx
    cbs
    cfv
    cB
    cop
    csn
    1str.g
    eqimss2i
    strfv
end
