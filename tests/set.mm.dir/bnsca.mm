include "cbn.mm"
include "wcel.mm"
include "cnvc.mm"
include "ccms.mm"
include "isbn.mm"
include "simp3bi.mm"

theorem bnsca
  let cF: class F
  let cW: class W
  let vw: setvar w
  assume isbn.1: |- F = ( Scalar ` W )


  assert |- ( W e. Ban -> F e. CMetSp )

  proof
    cW
    cbn
    wcel
    cW
    cnvc
    wcel
    cW
    ccms
    wcel
    cF
    ccms
    wcel
    cF
    cW
    isbn.1
    isbn
    simp3bi
end
