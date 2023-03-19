include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wa.mm"
include "eqidd.mm"
include "ccats1val2.mm"
include "mpd3an3.mm"

theorem ccatws1ls
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( W e. Word V /\ X e. V ) -> ( ( W ++ <" X "> ) ` ( # ` W ) ) = X )

  proof
    cW
    cV
    cword
    wcel
    #
    cX
    cV
    wcel
    #
    cW
    chash
    cfv
    #
    @2
    wceq
    @2
    cW
    cX
    cs1
    cconcat
    co
    cfv
    cX
    wceq
    @0
    @1
    wa
    @2
    eqidd
    cX
    @2
    cV
    cW
    ccats1val2
    mpd3an3
end
