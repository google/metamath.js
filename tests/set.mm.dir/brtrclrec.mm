include "wcel.mm"
include "cn.mm"
include "cvv.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "wrex.mm"
include "wb.mm"
include "nnex.mm"
include "briunov2.mm"
include "mpan2.mm"

theorem brtrclrec
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cV: class V
  let cX: class X
  let cY: class Y
  let vr: setvar r
  assume brtrclrec.def: |- C = ( r e. _V |-> U_ n e. NN ( r ^r n ) )

  disjoint n r
  disjoint R n
  disjoint R r
  disjoint X n
  disjoint Y n
  disjoint n r
  disjoint C n
  disjoint C r
  assert |- ( R e. V -> ( X ( C ` R ) Y <-> E. n e. NN X ( R ^r n ) Y ) )

  proof
    cR
    cV
    wcel
    cn
    cvv
    wcel
    cX
    cY
    cR
    cC
    cfv
    wbr
    cX
    cY
    cR
    vn
    cv
    crelexp
    co
    wbr
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
    cY
    vr
    brtrclrec.def
    briunov2
    mpan2
end
