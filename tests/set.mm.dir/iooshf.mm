include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cioo.mm"
include "wb.mm"
include "ltaddsub.mm"
include "3com13.mm"
include "3expa.mm"
include "adantrr.mm"
include "w3a.mm"
include "ltsubadd.mm"
include "bicomd.mm"
include "adantrl.mm"
include "anbi12d.mm"
include "cxr.mm"
include "readdcl.mm"
include "rexrd.mm"
include "ad2ant2rl.mm"
include "ad2ant2l.mm"
include "rexr.mm"
include "ad2antrl.mm"
include "elioo5.mm"
include "syl3anc.mm"
include "ancoms.mm"
include "ad2antll.mm"
include "resubcl.mm"
include "adantr.mm"
include "3bitr4rd.mm"

theorem iooshf
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A - B ) e. ( C (,) D ) <-> A e. ( ( C + B ) (,) ( D + B ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    wa
    #
    cC
    cB
    caddc
    co
    #
    cA
    clt
    wbr
    #
    cA
    cD
    cB
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    cC
    cA
    cB
    cmin
    co
    #
    clt
    wbr
    #
    @12
    cD
    clt
    wbr
    #
    wa
    #
    cA
    @7
    @9
    cioo
    co
    wcel
    #
    @12
    cC
    cD
    cioo
    co
    wcel
    #
    @6
    @8
    @13
    @10
    @14
    @2
    @3
    @8
    @13
    wb
    #
    @4
    @0
    @1
    @3
    @18
    @3
    @1
    @0
    @18
    cC
    cB
    cA
    ltaddsub
    3com13
    3expa
    adantrr
    @2
    @4
    @10
    @14
    wb
    #
    @3
    @0
    @1
    @4
    @19
    @0
    @1
    @4
    w3a
    @14
    @10
    cA
    cB
    cD
    ltsubadd
    bicomd
    3expa
    adantrl
    anbi12d
    @5
    @2
    @16
    @11
    wb
    #
    @5
    @2
    wa
    @7
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    @20
    @3
    @1
    @21
    @4
    @0
    @3
    @1
    wa
    @7
    cC
    cB
    readdcl
    rexrd
    ad2ant2rl
    @4
    @1
    @22
    @3
    @0
    @4
    @1
    wa
    @9
    cD
    cB
    readdcl
    rexrd
    ad2ant2l
    @0
    @23
    @5
    @1
    cA
    rexr
    ad2antrl
    @7
    @9
    cA
    elioo5
    syl3anc
    ancoms
    @6
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    @12
    cxr
    wcel
    #
    @17
    @15
    wb
    @3
    @24
    @2
    @4
    cC
    rexr
    ad2antrl
    @4
    @25
    @2
    @3
    cD
    rexr
    ad2antll
    @2
    @26
    @5
    @2
    @12
    cA
    cB
    resubcl
    rexrd
    adantr
    cC
    cD
    @12
    elioo5
    syl3anc
    3bitr4rd
end
