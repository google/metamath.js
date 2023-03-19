include "wcel.mm"
include "cn0.mm"
include "cvv.mm"
include "cfv.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "wrex.mm"
include "wb.mm"
include "nn0ex.mm"
include "eliunov2.mm"
include "mpan2.mm"

theorem elrtrclrec
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cV: class V
  let cX: class X
  let vr: setvar r
  assume rtrclrec.def: |- C = ( r e. _V |-> U_ n e. NN0 ( r ^r n ) )

  disjoint n r
  disjoint R n
  disjoint R r
  disjoint X n
  disjoint n r
  disjoint C n
  disjoint C r
  assert |- ( R e. V -> ( X e. ( C ` R ) <-> E. n e. NN0 X e. ( R ^r n ) ) )

  proof
    cR
    cV
    wcel
    cn0
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
    cn0
    wrex
    wb
    nn0ex
    cC
    cR
    cV
    vn
    crelexp
    cn0
    cvv
    cX
    vr
    rtrclrec.def
    eliunov2
    mpan2
end
