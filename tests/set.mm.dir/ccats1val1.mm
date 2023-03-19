include "wcel.mm"
include "cword.mm"
include "cs1.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cconcat.mm"
include "wceq.mm"
include "s1cl.mm"
include "ccatval1.mm"
include "syl3an2.mm"

theorem ccats1val1
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ S e. V /\ I e. ( 0 ..^ ( # ` W ) ) ) -> ( ( W ++ <" S "> ) ` I ) = ( W ` I ) )

  proof
    cS
    cV
    wcel
    cW
    cV
    cword
    #
    wcel
    cS
    cs1
    #
    @0
    wcel
    cI
    cc0
    cW
    chash
    cfv
    cfzo
    co
    wcel
    cI
    cW
    @1
    cconcat
    co
    cfv
    cI
    cW
    cfv
    wceq
    cS
    cV
    s1cl
    cV
    cW
    @1
    cI
    ccatval1
    syl3an2
end
