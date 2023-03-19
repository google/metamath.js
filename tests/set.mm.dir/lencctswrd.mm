include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "wrdcctswrd.mm"
include "fveq2d.mm"

theorem lencctswrd
  let cM: class M
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ M e. ( 0 ... ( # ` W ) ) ) -> ( # ` ( ( W substr <. 0 , M >. ) ++ ( W substr <. M , ( # ` W ) >. ) ) ) = ( # ` W ) )

  proof
    cW
    cV
    cword
    wcel
    cM
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    wa
    cW
    cc0
    cM
    cop
    csubstr
    co
    cW
    cM
    @0
    cop
    csubstr
    co
    cconcat
    co
    cW
    chash
    cM
    cV
    cW
    wrdcctswrd
    fveq2d
end
