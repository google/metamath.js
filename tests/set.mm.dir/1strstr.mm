include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "c1.mm"
include "cstr.mm"
include "1nn.mm"
include "basendx.mm"
include "strle1.mm"
include "eqbrtri.mm"

theorem 1strstr
  let cB: class B
  let cG: class G
  assume 1str.g: |- G = { <. ( Base ` ndx ) , B >. }


  assert |- G Struct <. 1 , 1 >.

  proof
    cG
    cnx
    cbs
    cfv
    #
    cB
    cop
    csn
    c1
    c1
    cop
    cstr
    1str.g
    @0
    c1
    cB
    1nn
    basendx
    strle1
    eqbrtri
end
