include "wcel.mm"
include "cn.mm"
include "cvv.mm"
include "cfv.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "wrex.mm"
include "wb.mm"
include "nnex.mm"
include "eliunov2.mm"
include "mpan2.mm"

theorem eltrclrec
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cV: class V
  let cX: class X
  let vr: setvar r
  assume trclrec.def: |- C = ( r e. _V |-> U_ n e. NN ( r ^r n ) )

  disjoint n r
  disjoint R n
  disjoint R r
  disjoint X n
  disjoint n r
  disjoint C n
  disjoint C r
  assert |- ( R e. V -> ( X e. ( C ` R ) <-> E. n e. NN X e. ( R ^r n ) ) )

  proof
    cR
    cV
    wcel
    cn
    cvv
    wcel
    cX
    cR
    cC
    cfv
    wcel
    cX
    cR
    vn
    cv
    crelexp
    co
    wcel
    vn
    cn
    wrex
    wb
    nnex
    cC
    cR
    cV
    vn
    crelexp
    cn
    cvv
    cX
    vr
    trclrec.def
    eliunov2
    mpan2
end
