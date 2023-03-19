include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "caddc.mm"
include "simpl.mm"
include "adantl.mm"
include "adantr.mm"
include "eluzelz.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "zsubcld.mm"
include "ancoms.mm"
include "zaddcld.mm"
include "cr.mm"
include "wi.mm"
include "zre.mm"
include "posdif.mm"
include "biimpd.mm"
include "syl2anr.mm"
include "adantld.mm"
include "imp.mm"
include "resubcl.mm"
include "syl2an.mm"
include "eluzelre.mm"
include "ad2antrl.mm"
include "ltaddposd.mm"
include "mpbid.mm"
include "cc.mm"
include "wb.mm"
include "zcn.mm"
include "eluzelcn.mm"
include "w3a.mm"
include "addsub12.mm"
include "breq2d.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "fzosubel3.mm"
include "syl2anc.mm"
include "ex.mm"

theorem eluzgtdifelfzo
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( N e. ( ZZ>= ` A ) /\ B < A ) -> ( N - A ) e. ( 0 ..^ ( N - B ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cN
    cA
    cuz
    cfv
    wcel
    #
    cB
    cA
    clt
    wbr
    #
    wa
    #
    cN
    cA
    cmin
    co
    cc0
    cN
    cB
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    @2
    @5
    wa
    #
    cN
    cA
    cA
    @6
    caddc
    co
    #
    cfzo
    co
    wcel
    #
    @6
    cz
    wcel
    #
    @7
    @8
    @3
    @9
    cz
    wcel
    cN
    @9
    clt
    wbr
    #
    @10
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @8
    cA
    @6
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    @5
    @2
    @11
    @5
    @2
    wa
    cN
    cB
    @3
    cN
    cz
    wcel
    @4
    @2
    cA
    cN
    eluzelz
    ad2antrr
    @5
    @0
    @1
    simprr
    zsubcld
    ancoms
    #
    zaddcld
    @8
    @12
    cN
    cN
    cA
    cB
    cmin
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    @8
    cc0
    @14
    clt
    wbr
    #
    @16
    @2
    @5
    @17
    @2
    @4
    @17
    @3
    @1
    cB
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @4
    @17
    wi
    @0
    cB
    zre
    #
    cA
    zre
    #
    @18
    @19
    wa
    @4
    @17
    cB
    cA
    posdif
    biimpd
    syl2anr
    adantld
    imp
    @8
    @14
    cN
    @2
    @14
    cr
    wcel
    #
    @5
    @0
    @19
    @18
    @22
    @1
    @21
    @20
    cA
    cB
    resubcl
    syl2an
    adantr
    @3
    cN
    cr
    wcel
    @2
    @4
    cA
    cN
    eluzelre
    ad2antrl
    ltaddposd
    mpbid
    @8
    cA
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @12
    @16
    wb
    @0
    @23
    @1
    @5
    cA
    zcn
    ad2antrr
    @3
    @24
    @2
    @4
    cA
    cN
    eluzelcn
    ad2antrl
    @2
    @25
    @5
    @1
    @25
    @0
    cB
    zcn
    adantl
    adantr
    @23
    @24
    @25
    w3a
    @9
    @15
    cN
    clt
    cA
    cN
    cB
    addsub12
    breq2d
    syl3anc
    mpbird
    cN
    cA
    @9
    elfzo2
    syl3anbrc
    @13
    cN
    cA
    @6
    fzosubel3
    syl2anc
    ex
end
