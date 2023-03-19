include "wcel.mm"
include "wa.mm"
include "cedg.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "edgval.mm"
include "struct2griedg.mm"
include "rneqd.mm"
include "syl5eq.mm"

theorem edgstruct
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  assume edgstruct.s: |- G = { <. ( Base ` ndx ) , V >. , <. ( .ef ` ndx ) , E >. }


  assert |- ( ( V e. W /\ E e. X ) -> ( Edg ` G ) = ran E )

  proof
    cV
    cW
    wcel
    cE
    cX
    wcel
    wa
    #
    cG
    cedg
    cfv
    cG
    ciedg
    cfv
    #
    crn
    cE
    crn
    cG
    edgval
    @0
    @1
    cE
    cE
    cG
    cV
    cW
    cX
    edgstruct.s
    struct2griedg
    rneqd
    syl5eq
end
