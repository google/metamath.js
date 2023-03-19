include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wnel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "clsw.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "lsw.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "cfzo.mm"
include "wf.mm"
include "cn0.mm"
include "wrdf.mm"
include "lencl.mm"
include "wa.mm"
include "simpll.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "elnnne0.mm"
include "biimpri.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0re.mm"
include "ltm1d.mm"
include "adantr.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "ex.mm"
include "syl2anc.mm"
include "wn.mm"
include "eleq1a.mm"
include "com12.mm"
include "eqcoms.mm"
include "nnel.mm"
include "syl6ibr.mm"
include "necon2ad.mm"
include "syl6.mm"
include "com23.mm"
include "3imp.mm"
include "eqnetrd.mm"

theorem lswn0
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ (/) e/ V /\ ( # ` W ) =/= 0 ) -> ( lastS ` W ) =/= (/) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    c0
    cV
    wnel
    #
    cW
    chash
    cfv
    #
    cc0
    wne
    #
    w3a
    cW
    clsw
    cfv
    #
    @3
    c1
    cmin
    co
    #
    cW
    cfv
    #
    c0
    @1
    @2
    @5
    @7
    wceq
    @4
    cW
    @0
    lsw
    3ad2ant1
    @1
    @2
    @4
    @7
    c0
    wne
    #
    @1
    @4
    @2
    @8
    @1
    @4
    @7
    cV
    wcel
    #
    @2
    @8
    wi
    @1
    cc0
    @3
    cfzo
    co
    #
    cV
    cW
    wf
    #
    @3
    cn0
    wcel
    #
    @4
    @9
    wi
    cV
    cW
    wrdf
    cV
    cW
    lencl
    @11
    @12
    wa
    #
    @4
    @9
    @13
    @4
    wa
    @10
    cV
    @6
    cW
    @11
    @12
    @4
    simpll
    @12
    @4
    @6
    @10
    wcel
    #
    @11
    @12
    @4
    wa
    #
    @6
    cn0
    wcel
    #
    @3
    cn
    wcel
    #
    @6
    @3
    clt
    wbr
    #
    @14
    @15
    @17
    @16
    @17
    @15
    @3
    elnnne0
    biimpri
    #
    @3
    nnm1nn0
    syl
    @19
    @12
    @18
    @4
    @12
    @3
    @3
    nn0re
    ltm1d
    adantr
    @6
    @3
    elfzo0
    syl3anbrc
    adantll
    ffvelrnd
    ex
    syl2anc
    @9
    @2
    @7
    c0
    @9
    @7
    c0
    wceq
    #
    c0
    cV
    wcel
    #
    @2
    wn
    @20
    @9
    @21
    @9
    @21
    wi
    c0
    @7
    @9
    c0
    @7
    wceq
    @21
    @7
    cV
    c0
    eleq1a
    com12
    eqcoms
    com12
    c0
    cV
    nnel
    syl6ibr
    necon2ad
    syl6
    com23
    3imp
    eqnetrd
end
