include "cn.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "clt.mm"
include "c1.mm"
include "cfz.mm"
include "cc0.mm"
include "cfzo.mm"
include "simp3.mm"
include "wa.mm"
include "wb.mm"
include "nnnn0.mm"
include "anim12i.mm"
include "3adant3.mm"
include "nn0sub.mm"
include "syl.mm"
include "mpbid.mm"
include "simp2.mm"
include "nngt0.mm"
include "3ad2ant1.mm"
include "cr.mm"
include "nnre.mm"
include "ltsubpos.mm"
include "3jca.mm"
include "elfz1b.mm"
include "elfzo0.mm"
include "3imtr4i.mm"

theorem ubmelfzo
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 1 ... N ) -> ( N - K ) e. ( 0 ..^ N ) )

  proof
    cK
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cK
    cN
    cle
    wbr
    #
    w3a
    #
    cN
    cK
    cmin
    co
    #
    cn0
    wcel
    #
    @1
    @4
    cN
    clt
    wbr
    #
    w3a
    cK
    c1
    cN
    cfz
    co
    wcel
    @4
    cc0
    cN
    cfzo
    co
    wcel
    @3
    @5
    @1
    @6
    @3
    @2
    @5
    @0
    @1
    @2
    simp3
    @3
    cK
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    @2
    @5
    wb
    @0
    @1
    @9
    @2
    @0
    @7
    @1
    @8
    cK
    nnnn0
    cN
    nnnn0
    anim12i
    3adant3
    cK
    cN
    nn0sub
    syl
    mpbid
    @0
    @1
    @2
    simp2
    @3
    cc0
    cK
    clt
    wbr
    #
    @6
    @0
    @1
    @10
    @2
    cK
    nngt0
    3ad2ant1
    @3
    cK
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    wa
    #
    @10
    @6
    wb
    @0
    @1
    @13
    @2
    @0
    @11
    @1
    @12
    cK
    nnre
    cN
    nnre
    anim12i
    3adant3
    cK
    cN
    ltsubpos
    syl
    mpbid
    3jca
    cN
    cK
    elfz1b
    @4
    cN
    elfzo0
    3imtr4i
end
