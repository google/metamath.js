include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "wn.mm"
include "wa.mm"
include "caddc.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "syl2an.mm"
include "3adant3.mm"
include "elfzonelfzo.mm"
include "imp.mm"
include "sylan.mm"
include "wb.mm"
include "cc.mm"
include "wceq.mm"
include "nn0cn.mm"
include "zcn.mm"
include "npncan3.mm"
include "syl3an.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"

theorem swrdccatin12lem1
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N


  assert |- ( ( L e. NN0 /\ M e. NN0 /\ N e. ZZ ) -> ( ( K e. ( 0 ..^ ( N - M ) ) /\ -. K e. ( 0 ..^ ( L - M ) ) ) -> K e. ( ( L - M ) ..^ ( ( L - M ) + ( N - L ) ) ) ) )

  proof
    cL
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cK
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    wcel
    cK
    cc0
    cL
    cM
    cmin
    co
    #
    cfzo
    co
    wcel
    wn
    wa
    #
    cK
    @5
    @5
    cN
    cL
    cmin
    co
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @3
    @6
    wa
    @9
    cK
    @5
    @4
    cfzo
    co
    #
    wcel
    #
    @3
    @5
    cz
    wcel
    #
    @6
    @11
    @0
    @1
    @12
    @2
    @0
    cL
    cz
    wcel
    cM
    cz
    wcel
    @12
    @1
    cL
    nn0z
    cM
    nn0z
    cL
    cM
    zsubcl
    syl2an
    3adant3
    @12
    @6
    @11
    @4
    cK
    cc0
    @5
    elfzonelfzo
    imp
    sylan
    @3
    @9
    @11
    wb
    @6
    @3
    @8
    @10
    cK
    @3
    @7
    @4
    @5
    cfzo
    @0
    cL
    cc
    wcel
    @1
    cM
    cc
    wcel
    @2
    cN
    cc
    wcel
    @7
    @4
    wceq
    cL
    nn0cn
    cM
    nn0cn
    cN
    zcn
    cL
    cM
    cN
    npncan3
    syl3an
    oveq2d
    eleq2d
    adantr
    mpbird
    ex
end
