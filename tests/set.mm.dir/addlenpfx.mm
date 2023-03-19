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
include "caddc.mm"
include "cmin.mm"
include "pfxlen.mm"
include "swrdrlen.mm"
include "oveq12d.mm"
include "cc.mm"
include "wceq.mm"
include "elfznn0.mm"
include "nn0cnd.mm"
include "lencl.mm"
include "pncan3.mm"
include "syl2anr.mm"
include "eqtrd.mm"

theorem addlenpfx
  let cM: class M
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ M e. ( 0 ... ( # ` W ) ) ) -> ( ( # ` ( W prefix M ) ) + ( # ` ( W substr <. M , ( # ` W ) >. ) ) ) = ( # ` W ) )

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
    wcel
    #
    wa
    #
    cW
    cM
    cpfx
    co
    chash
    cfv
    #
    cW
    cM
    @1
    cop
    csubstr
    co
    chash
    cfv
    #
    caddc
    co
    cM
    @1
    cM
    cmin
    co
    #
    caddc
    co
    #
    @1
    @3
    @4
    cM
    @5
    @6
    caddc
    cV
    cW
    cM
    pfxlen
    cM
    cV
    cW
    swrdrlen
    oveq12d
    @2
    cM
    cc
    wcel
    @1
    cc
    wcel
    @7
    @1
    wceq
    @0
    @2
    cM
    cM
    @1
    elfznn0
    nn0cnd
    @0
    @1
    cV
    cW
    lencl
    nn0cnd
    cM
    @1
    pncan3
    syl2anr
    eqtrd
end
