include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cmin.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "elfzle1.mm"
include "adantr.mm"
include "cn0.mm"
include "elfz3nn0.mm"
include "nn0zd.mm"
include "zred.mm"
include "cz.mm"
include "elfzelz.mm"
include "subge02d.mm"
include "mpbid.mm"
include "wb.mm"
include "zsubcld.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "fzss2.mm"
include "syl.mm"
include "simpr.mm"
include "sseldd.mm"
include "adantl.mm"
include "elfzle2.mm"
include "lesubd.mm"
include "elfzuz.mm"
include "elfz5.mm"
include "jca.mm"

theorem fsum0diaglem
  let vj: setvar j
  let vk: setvar k
  let cN: class N

  disjoint j k
  disjoint N j
  disjoint N k
  assert |- ( ( j e. ( 0 ... N ) /\ k e. ( 0 ... ( N - j ) ) ) -> ( k e. ( 0 ... N ) /\ j e. ( 0 ... ( N - k ) ) ) )

  proof
    vj
    cv
    #
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    vk
    cv
    #
    cc0
    cN
    @0
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @3
    @1
    wcel
    @0
    cc0
    cN
    @3
    cmin
    co
    #
    cfz
    co
    wcel
    #
    @7
    @5
    @1
    @3
    @7
    cN
    @4
    cuz
    cfv
    wcel
    #
    @5
    @1
    wss
    @7
    @10
    @4
    cN
    cle
    wbr
    #
    @7
    cc0
    @0
    cle
    wbr
    #
    @11
    @2
    @12
    @6
    @0
    cc0
    cN
    elfzle1
    adantr
    @7
    cN
    @0
    @7
    cN
    @7
    cN
    @2
    cN
    cn0
    wcel
    @6
    @0
    cN
    elfz3nn0
    adantr
    nn0zd
    #
    zred
    #
    @7
    @0
    @2
    @0
    cz
    wcel
    @6
    @0
    cc0
    cN
    elfzelz
    adantr
    #
    zred
    #
    subge02d
    mpbid
    @7
    @4
    cz
    wcel
    cN
    cz
    wcel
    @10
    @11
    wb
    @7
    cN
    @0
    @13
    @15
    zsubcld
    @13
    @4
    cN
    eluz
    syl2anc
    mpbird
    @4
    cc0
    cN
    fzss2
    syl
    @2
    @6
    simpr
    sseldd
    @7
    @9
    @0
    @8
    cle
    wbr
    #
    @7
    @3
    cN
    @0
    @7
    @3
    @6
    @3
    cz
    wcel
    @2
    @3
    cc0
    @4
    elfzelz
    adantl
    #
    zred
    @14
    @16
    @6
    @3
    @4
    cle
    wbr
    @2
    @3
    cc0
    @4
    elfzle2
    adantl
    lesubd
    @7
    @0
    cc0
    cuz
    cfv
    wcel
    #
    @8
    cz
    wcel
    @9
    @17
    wb
    @2
    @19
    @6
    @0
    cc0
    cN
    elfzuz
    adantr
    @7
    cN
    @3
    @13
    @18
    zsubcld
    @0
    cc0
    @8
    elfz5
    syl2anc
    mpbird
    jca
end
