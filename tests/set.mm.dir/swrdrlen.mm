include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "cmin.mm"
include "wceq.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "adantr.mm"
include "swrdlen.mm"
include "mpd3an3.mm"

theorem swrdrlen
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ I e. ( 0 ... ( # ` W ) ) ) -> ( # ` ( W substr <. I , ( # ` W ) >. ) ) = ( ( # ` W ) - I ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cI
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @1
    @2
    wcel
    #
    cW
    cI
    @1
    cop
    csubstr
    co
    chash
    cfv
    @1
    cI
    cmin
    co
    wceq
    @0
    @4
    @3
    @0
    @1
    cn0
    wcel
    @4
    cV
    cW
    lencl
    @1
    nn0fz0
    sylib
    adantr
    cV
    cW
    cI
    @1
    swrdlen
    mpd3an3
end
