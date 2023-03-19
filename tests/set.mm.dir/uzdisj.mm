include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cuz.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
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
include "peano2zm.mm"
include "lenltd.mm"
include "pm2.21dd.mm"
include "ssriv.mm"
include "ss0.mm"
include "ax-mp.mm"

theorem uzdisj
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( ( M ... ( N - 1 ) ) i^i ( ZZ>= ` N ) ) = (/)

  proof
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cN
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
    @0
    @4
    clt
    wbr
    #
    @4
    c0
    wcel
    @5
    cN
    @4
    cle
    wbr
    #
    @6
    @5
    @4
    @2
    wcel
    #
    @7
    @5
    @4
    @1
    wcel
    #
    @8
    @4
    @1
    @2
    elin
    #
    simprbi
    #
    cN
    @4
    eluzle
    syl
    @5
    cN
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @7
    @6
    wb
    @5
    @8
    @12
    @11
    cN
    @4
    eluzel2
    syl
    #
    @5
    @8
    @13
    @11
    cN
    @4
    eluzelz
    syl
    #
    cN
    @4
    zlem1lt
    syl2anc
    mpbid
    @5
    @4
    @0
    cle
    wbr
    #
    @6
    wn
    @5
    @9
    @16
    @5
    @9
    @8
    @10
    simplbi
    @4
    cM
    @0
    elfzle2
    syl
    @5
    @4
    @0
    @5
    @4
    @15
    zred
    @5
    @0
    @5
    @12
    @0
    cz
    wcel
    @14
    cN
    peano2zm
    syl
    zred
    lenltd
    mpbid
    pm2.21dd
    ssriv
    @3
    ss0
    ax-mp
end
