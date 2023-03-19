include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "0nn0.mm"
include "ccat2s1fvw.mm"
include "mp3anl2.mm"

theorem ccat2s1fst
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( W e. Word V /\ 0 < ( # ` W ) ) /\ ( X e. V /\ Y e. V ) ) -> ( ( ( W ++ <" X "> ) ++ <" Y "> ) ` 0 ) = ( W ` 0 ) )

  proof
    cW
    cV
    cword
    wcel
    cc0
    cn0
    wcel
    cc0
    cW
    chash
    cfv
    clt
    wbr
    cX
    cV
    wcel
    cY
    cV
    wcel
    wa
    cc0
    cW
    cX
    cs1
    cconcat
    co
    cY
    cs1
    cconcat
    co
    cfv
    cc0
    cW
    cfv
    wceq
    0nn0
    cc0
    cV
    cW
    cX
    cY
    ccat2s1fvw
    mp3anl2
end
