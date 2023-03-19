include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "cn0.mm"
include "elfznn0.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "adantl.mm"
include "swrd0swrd0.mm"
include "mpd3an3.mm"

theorem swrd0swrdid
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) ) -> ( ( W substr <. 0 , N >. ) substr <. 0 , N >. ) = ( W substr <. 0 , N >. ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    cN
    cc0
    cN
    cfz
    co
    wcel
    #
    cW
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    @4
    csubstr
    co
    @5
    wceq
    @2
    @3
    @0
    @2
    cN
    cn0
    wcel
    @3
    cN
    @1
    elfznn0
    cN
    nn0fz0
    sylib
    adantl
    cN
    cN
    cV
    cW
    swrd0swrd0
    mpd3an3
end
