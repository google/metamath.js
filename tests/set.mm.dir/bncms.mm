include "cbn.mm"
include "wcel.mm"
include "cnvc.mm"
include "ccms.mm"
include "csca.mm"
include "cfv.mm"
include "eqid.mm"
include "isbn.mm"
include "simp2bi.mm"

theorem bncms
  let cW: class W


  assert |- ( W e. Ban -> W e. CMetSp )

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
    cW
    csca
    cfv
    #
    ccms
    wcel
    @0
    cW
    @0
    eqid
    isbn
    simp2bi
end
