include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cpfx.mm"
include "wceq.mm"
include "cn0.mm"
include "elfznn0.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "adantl.mm"
include "pfxpfx.mm"
include "mpd3an3.mm"

theorem pfxpfxid
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) ) -> ( ( W prefix N ) prefix N ) = ( W prefix N ) )

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
    cN
    cpfx
    co
    #
    cN
    cpfx
    co
    @4
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
    pfxpfx
    mpd3an3
end
