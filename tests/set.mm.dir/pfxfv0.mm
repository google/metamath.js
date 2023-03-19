include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "cpfx.mm"
include "wceq.mm"
include "simpl.mm"
include "cuz.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "sseli.mm"
include "adantl.mm"
include "cn.mm"
include "elfznn.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "pfxfv.mm"
include "syl3anc.mm"

theorem pfxfv0
  let cL: class L
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ L e. ( 1 ... ( # ` W ) ) ) -> ( ( W prefix L ) ` 0 ) = ( W ` 0 ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cL
    c1
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
    #
    @0
    cL
    cc0
    @1
    cfz
    co
    #
    wcel
    #
    cc0
    cc0
    cL
    cfzo
    co
    wcel
    #
    cc0
    cW
    cL
    cpfx
    co
    cfv
    cc0
    cW
    cfv
    wceq
    @0
    @3
    simpl
    @3
    @6
    @0
    @2
    @5
    cL
    c1
    cc0
    cuz
    cfv
    wcel
    @2
    @5
    wss
    1eluzge0
    c1
    cc0
    @1
    fzss1
    ax-mp
    sseli
    adantl
    @4
    cL
    cn
    wcel
    #
    @7
    @3
    @8
    @0
    cL
    @1
    elfznn
    adantl
    cL
    lbfzo0
    sylibr
    cc0
    cL
    cV
    cW
    pfxfv
    syl3anc
end
