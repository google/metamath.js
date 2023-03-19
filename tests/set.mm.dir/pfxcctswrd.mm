include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cpfx.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "wceq.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "adantr.mm"
include "ccatpfx.mm"
include "mpd3an3.mm"
include "pfxid.mm"
include "eqtrd.mm"

theorem pfxcctswrd
  let cM: class M
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ M e. ( 0 ... ( # ` W ) ) ) -> ( ( W prefix M ) ++ ( W substr <. M , ( # ` W ) >. ) ) = W )

  proof
    cW
    cV
    cword
    wcel
    #
    cM
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
    wa
    cW
    cM
    cpfx
    co
    cW
    cM
    @1
    cop
    csubstr
    co
    cconcat
    co
    #
    cW
    @1
    cpfx
    co
    #
    cW
    @0
    @3
    @1
    @2
    wcel
    #
    @4
    @5
    wceq
    @0
    @6
    @3
    @0
    @1
    cn0
    wcel
    @6
    cV
    cW
    lencl
    @1
    nn0fz0
    sylib
    adantr
    cV
    cW
    cM
    @1
    ccatpfx
    mpd3an3
    @0
    @5
    cW
    wceq
    @3
    cV
    cW
    pfxid
    adantr
    eqtrd
end
