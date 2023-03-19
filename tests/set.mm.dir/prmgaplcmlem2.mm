include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "clcmf.mm"
include "cfv.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "cgcd.mm"
include "clt.mm"
include "elfzuz.mm"
include "adantl.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "anbi12d.mm"
include "prmgaplcmlem1.mm"
include "cz.mm"
include "elfzelz.mm"
include "iddvds.mm"
include "syl.mm"
include "jca.mm"
include "rspcedvd.mm"
include "wss.mm"
include "cfn.mm"
include "cc0.mm"
include "wnel.mm"
include "fzssz.mm"
include "a1i.mm"
include "fzfid.mm"
include "0nelfz1.mm"
include "lcmfn0cl.mm"
include "syl3anc.mm"
include "adantr.mm"
include "eluz2nn.mm"
include "nnaddcld.mm"
include "ncoprmgcdgt1b.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem prmgaplcmlem2
  let cI: class I
  let cN: class N
  let vx: setvar x
  let vi: setvar i


  assert |- ( ( N e. NN /\ I e. ( 2 ... N ) ) -> 1 < ( ( ( _lcm ` ( 1 ... N ) ) + I ) gcd I ) )

  proof
    cN
    cn
    wcel
    #
    cI
    c2
    cN
    cfz
    co
    wcel
    #
    wa
    #
    vi
    cv
    #
    c1
    cN
    cfz
    co
    #
    clcmf
    cfv
    #
    cI
    caddc
    co
    #
    cdvds
    wbr
    #
    @3
    cI
    cdvds
    wbr
    #
    wa
    #
    vi
    c2
    cuz
    cfv
    #
    wrex
    #
    c1
    @6
    cI
    cgcd
    co
    clt
    wbr
    #
    @2
    @9
    cI
    @6
    cdvds
    wbr
    #
    cI
    cI
    cdvds
    wbr
    #
    wa
    #
    vi
    cI
    @10
    @1
    cI
    @10
    wcel
    #
    @0
    cI
    c2
    cN
    elfzuz
    #
    adantl
    @3
    cI
    wceq
    #
    @9
    @15
    wb
    @2
    @18
    @7
    @13
    @8
    @14
    @3
    cI
    @6
    cdvds
    breq1
    @3
    cI
    cI
    cdvds
    breq1
    anbi12d
    adantl
    @2
    @13
    @14
    cI
    cN
    prmgaplcmlem1
    @1
    @14
    @0
    @1
    cI
    cz
    wcel
    @14
    cI
    c2
    cN
    elfzelz
    cI
    iddvds
    syl
    adantl
    jca
    rspcedvd
    @2
    @6
    cn
    wcel
    cI
    cn
    wcel
    #
    @11
    @12
    wb
    @2
    @5
    cI
    @0
    @5
    cn
    wcel
    #
    @1
    @0
    @4
    cz
    wss
    #
    @4
    cfn
    wcel
    cc0
    @4
    wnel
    #
    @20
    @21
    @0
    c1
    cN
    fzssz
    a1i
    @0
    c1
    cN
    fzfid
    @22
    @0
    cN
    0nelfz1
    a1i
    @4
    lcmfn0cl
    syl3anc
    adantr
    @1
    @19
    @0
    @1
    @16
    @19
    @17
    cI
    eluz2nn
    syl
    adantl
    #
    nnaddcld
    @23
    @6
    cI
    vi
    ncoprmgcdgt1b
    syl2anc
    mpbid
end
