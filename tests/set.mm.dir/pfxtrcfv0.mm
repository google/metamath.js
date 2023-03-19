include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "cpfx.mm"
include "wceq.mm"
include "simpl.mm"
include "wrdlenge2n0.mm"
include "cn.mm"
include "cuz.mm"
include "cz.mm"
include "2z.mm"
include "a1i.mm"
include "lencl.mm"
include "nn0zd.mm"
include "adantr.mm"
include "simpr.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "uz2m1nn.mm"
include "syl.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "pfxtrcfv.mm"
include "syl3anc.mm"

theorem pfxtrcfv0
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ 2 <_ ( # ` W ) ) -> ( ( W prefix ( ( # ` W ) - 1 ) ) ` 0 ) = ( W ` 0 ) )

  proof
    cW
    cV
    cword
    wcel
    #
    c2
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @0
    cW
    c0
    wne
    cc0
    cc0
    @1
    c1
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    cc0
    cW
    @4
    cpfx
    co
    cfv
    cc0
    cW
    cfv
    wceq
    @0
    @2
    simpl
    cV
    cW
    wrdlenge2n0
    @3
    @4
    cn
    wcel
    #
    @5
    @3
    @1
    c2
    cuz
    cfv
    wcel
    #
    @6
    @3
    c2
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @2
    @7
    @8
    @3
    2z
    a1i
    @0
    @9
    @2
    @0
    @1
    cV
    cW
    lencl
    nn0zd
    adantr
    @0
    @2
    simpr
    c2
    @1
    eluz2
    syl3anbrc
    @1
    uz2m1nn
    syl
    @4
    lbfzo0
    sylibr
    cc0
    cV
    cW
    pfxtrcfv
    syl3anc
end
