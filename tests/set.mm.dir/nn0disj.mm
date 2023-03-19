include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "elin.mm"
include "simprbi.mm"
include "eluzle.mm"
include "syl.mm"
include "cz.mm"
include "wb.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "zlem1lt.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wn.mm"
include "simplbi.mm"
include "elfzle2.mm"
include "zred.mm"
include "wa.mm"
include "elfzel2.mm"
include "adantr.mm"
include "sylbi.mm"
include "lenltd.mm"
include "cc.mm"
include "zcnd.mm"
include "pncan1.mm"
include "eqcomd.mm"
include "breq1d.mm"
include "notbid.mm"
include "bitrd.mm"
include "pm2.21dd.mm"
include "ssriv.mm"
include "ss0.mm"
include "ax-mp.mm"

theorem nn0disj
  let cN: class N
  let vk: setvar k


  assert |- ( ( 0 ... N ) i^i ( ZZ>= ` ( N + 1 ) ) ) = (/)

  proof
    cc0
    cN
    cfz
    co
    #
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cin
    #
    c0
    wss
    @3
    c0
    wceq
    vk
    @3
    c0
    vk
    cv
    #
    @3
    wcel
    #
    @1
    c1
    cmin
    co
    #
    @4
    clt
    wbr
    #
    @4
    c0
    wcel
    @5
    @1
    @4
    cle
    wbr
    #
    @7
    @5
    @4
    @2
    wcel
    #
    @8
    @5
    @4
    @0
    wcel
    #
    @9
    @4
    @0
    @2
    elin
    #
    simprbi
    #
    @1
    @4
    eluzle
    syl
    @5
    @1
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @8
    @7
    wb
    @5
    @9
    @13
    @12
    @1
    @4
    eluzel2
    syl
    @5
    @9
    @14
    @12
    @1
    @4
    eluzelz
    syl
    #
    @1
    @4
    zlem1lt
    syl2anc
    mpbid
    @5
    @4
    cN
    cle
    wbr
    #
    @7
    wn
    #
    @5
    @10
    @16
    @5
    @10
    @9
    @11
    simplbi
    @4
    cc0
    cN
    elfzle2
    syl
    @5
    @16
    cN
    @4
    clt
    wbr
    #
    wn
    @17
    @5
    @4
    cN
    @5
    @4
    @15
    zred
    @5
    cN
    @5
    @10
    @9
    wa
    cN
    cz
    wcel
    #
    @11
    @10
    @19
    @9
    @4
    cc0
    cN
    elfzel2
    adantr
    sylbi
    #
    zred
    lenltd
    @5
    @18
    @7
    @5
    cN
    @6
    @4
    clt
    @5
    @6
    cN
    @5
    cN
    cc
    wcel
    @6
    cN
    wceq
    @5
    cN
    @20
    zcnd
    cN
    pncan1
    syl
    eqcomd
    breq1d
    notbid
    bitrd
    mpbid
    pm2.21dd
    ssriv
    @3
    ss0
    ax-mp
end
