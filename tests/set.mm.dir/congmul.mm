include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2l.mm"
include "zmulcld.mm"
include "simp2r.mm"
include "simp13.mm"
include "simp3r.mm"
include "wi.mm"
include "zsubcl.mm"
include "3ad2ant2.mm"
include "dvdsmultr2.mm"
include "syl3anc.mm"
include "mpd.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "adantl.mm"
include "subdid.mm"
include "breqtrd.mm"
include "simp3l.mm"
include "zsubcld.mm"
include "dvdsmultr1.mm"
include "3ad2ant3.mm"
include "subdird.mm"
include "congtr.mm"
include "syl222anc.mm"

theorem congmul
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ ) /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B x. D ) - ( C x. E ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    #
    cD
    cz
    wcel
    #
    cE
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    cA
    cD
    cE
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    w3a
    #
    @0
    cB
    cD
    cmul
    co
    #
    cz
    wcel
    cB
    cE
    cmul
    co
    #
    cz
    wcel
    cC
    cE
    cmul
    co
    #
    cz
    wcel
    cA
    @13
    @14
    cmin
    co
    #
    cdvds
    wbr
    cA
    @14
    @15
    cmin
    co
    #
    cdvds
    wbr
    cA
    @13
    @15
    cmin
    co
    cdvds
    wbr
    @0
    @1
    @2
    @6
    @11
    simp11
    #
    @12
    cB
    cD
    @0
    @1
    @2
    @6
    @11
    simp12
    #
    @3
    @4
    @5
    @11
    simp2l
    zmulcld
    @12
    cB
    cE
    @19
    @3
    @4
    @5
    @11
    simp2r
    #
    zmulcld
    @12
    cC
    cE
    @0
    @1
    @2
    @6
    @11
    simp13
    #
    @20
    zmulcld
    @12
    cA
    cB
    @9
    cmul
    co
    #
    @16
    cdvds
    @12
    @10
    cA
    @22
    cdvds
    wbr
    #
    @3
    @6
    @8
    @10
    simp3r
    @12
    @0
    @1
    @9
    cz
    wcel
    #
    @10
    @23
    wi
    @18
    @19
    @6
    @3
    @24
    @11
    cD
    cE
    zsubcl
    3ad2ant2
    cA
    cB
    @9
    dvdsmultr2
    syl3anc
    mpd
    @12
    cB
    cD
    cE
    @3
    @6
    cB
    cc
    wcel
    #
    @11
    @1
    @0
    @25
    @2
    cB
    zcn
    3ad2ant2
    3ad2ant1
    #
    @6
    @3
    cD
    cc
    wcel
    #
    @11
    @4
    @27
    @5
    cD
    zcn
    adantr
    3ad2ant2
    @6
    @3
    cE
    cc
    wcel
    #
    @11
    @5
    @28
    @4
    cE
    zcn
    adantl
    3ad2ant2
    #
    subdid
    breqtrd
    @12
    cA
    @7
    cE
    cmul
    co
    #
    @17
    cdvds
    @12
    @8
    cA
    @30
    cdvds
    wbr
    #
    @3
    @6
    @8
    @10
    simp3l
    @12
    @0
    @7
    cz
    wcel
    @5
    @8
    @31
    wi
    @18
    @12
    cB
    cC
    @19
    @21
    zsubcld
    @20
    cA
    @7
    cE
    dvdsmultr1
    syl3anc
    mpd
    @12
    cB
    cC
    cE
    @26
    @3
    @6
    cC
    cc
    wcel
    #
    @11
    @2
    @0
    @32
    @1
    cC
    zcn
    3ad2ant3
    3ad2ant1
    @29
    subdird
    breqtrd
    cA
    @13
    @14
    @15
    congtr
    syl222anc
end
