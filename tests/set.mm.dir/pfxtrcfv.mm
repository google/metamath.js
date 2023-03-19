include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "c0.mm"
include "wne.mm"
include "cfzo.mm"
include "cpfx.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cfn.mm"
include "wrdfin.mm"
include "1elfz0hash.mm"
include "sylan.mm"
include "cn.mm"
include "lennncl.mm"
include "elfz1end.mm"
include "sylib.mm"
include "jca.mm"
include "3adant3.mm"
include "fz0fzdiffz0.mm"
include "syl.mm"
include "pfxfv.mm"
include "syld3an2.mm"

theorem pfxtrcfv
  let cI: class I
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ W =/= (/) /\ I e. ( 0 ..^ ( ( # ` W ) - 1 ) ) ) -> ( ( W prefix ( ( # ` W ) - 1 ) ) ` I ) = ( W ` I ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cc0
    @1
    cfz
    co
    #
    wcel
    #
    cW
    c0
    wne
    #
    cI
    cc0
    @2
    cfzo
    co
    wcel
    #
    cI
    cW
    @2
    cpfx
    co
    cfv
    cI
    cW
    cfv
    wceq
    @0
    @5
    @6
    w3a
    c1
    @3
    wcel
    #
    @1
    c1
    @1
    cfz
    co
    wcel
    #
    wa
    #
    @4
    @0
    @5
    @9
    @6
    @0
    @5
    wa
    #
    @7
    @8
    @0
    cW
    cfn
    wcel
    @5
    @7
    cV
    cW
    wrdfin
    cW
    1elfz0hash
    sylan
    @10
    @1
    cn
    wcel
    @8
    cV
    cW
    lennncl
    @1
    elfz1end
    sylib
    jca
    3adant3
    @1
    c1
    @1
    fz0fzdiffz0
    syl
    cI
    @2
    cV
    cW
    pfxfv
    syld3an2
end
