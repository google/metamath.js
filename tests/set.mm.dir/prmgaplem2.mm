include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cfa.mm"
include "cfv.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "c1.mm"
include "cgcd.mm"
include "clt.mm"
include "elfzuz.mm"
include "adantl.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "anbi12d.mm"
include "prmgaplem1.mm"
include "cz.mm"
include "elfzelz.mm"
include "iddvds.mm"
include "syl.mm"
include "jca.mm"
include "rspcedvd.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "adantr.mm"
include "eluz2nn.mm"
include "nnaddcld.mm"
include "ncoprmgcdgt1b.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem prmgaplem2
  let cI: class I
  let cN: class N
  let vi: setvar i


  assert |- ( ( N e. NN /\ I e. ( 2 ... N ) ) -> 1 < ( ( ( ! ` N ) + I ) gcd I ) )

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
    cN
    cfa
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
    @5
    cI
    cgcd
    co
    clt
    wbr
    #
    @2
    @8
    cI
    @5
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
    @9
    @1
    cI
    @9
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
    @8
    @14
    wb
    @2
    @17
    @6
    @12
    @7
    @13
    @3
    cI
    @5
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
    @12
    @13
    cI
    cN
    prmgaplem1
    @1
    @13
    @0
    @1
    cI
    cz
    wcel
    @13
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
    @5
    cn
    wcel
    cI
    cn
    wcel
    #
    @10
    @11
    wb
    @2
    @4
    cI
    @0
    @4
    cn
    wcel
    #
    @1
    @0
    cN
    cn0
    wcel
    @19
    cN
    nnnn0
    cN
    faccl
    syl
    adantr
    @1
    @18
    @0
    @1
    @15
    @18
    @16
    cI
    eluz2nn
    syl
    adantl
    #
    nnaddcld
    @20
    @5
    cI
    vi
    ncoprmgcdgt1b
    syl2anc
    mpbid
end
