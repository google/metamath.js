include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "adantr.mm"
include "simpll.mm"
include "simprl.mm"
include "zmulcld.mm"
include "simplr.mm"
include "simprr.mm"
include "gcddvds.mm"
include "simpld.mm"
include "w3a.mm"
include "dvdsmultr1.mm"
include "imp.mm"
include "syl31anc.mm"
include "simprd.mm"
include "dvds2add.mm"
include "syl32anc.mm"

theorem bezoutr
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( X e. ZZ /\ Y e. ZZ ) ) -> ( A gcd B ) || ( ( A x. X ) + ( B x. Y ) ) )

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
    cX
    cz
    wcel
    #
    cY
    cz
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cgcd
    co
    #
    cz
    wcel
    #
    cA
    cX
    cmul
    co
    #
    cz
    wcel
    #
    cB
    cY
    cmul
    co
    #
    cz
    wcel
    #
    @7
    @9
    cdvds
    wbr
    #
    @7
    @11
    cdvds
    wbr
    #
    @7
    @9
    @11
    caddc
    co
    cdvds
    wbr
    #
    @2
    @8
    @5
    @2
    @7
    cA
    cB
    gcdcl
    nn0zd
    adantr
    #
    @6
    cA
    cX
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    zmulcld
    @6
    cB
    cY
    @0
    @1
    @5
    simplr
    #
    @2
    @3
    @4
    simprr
    #
    zmulcld
    @6
    @8
    @0
    @3
    @7
    cA
    cdvds
    wbr
    #
    @13
    @16
    @17
    @18
    @6
    @21
    @7
    cB
    cdvds
    wbr
    #
    @2
    @21
    @22
    wa
    @5
    cA
    cB
    gcddvds
    adantr
    #
    simpld
    @8
    @0
    @3
    w3a
    @21
    @13
    @7
    cA
    cX
    dvdsmultr1
    imp
    syl31anc
    @6
    @8
    @1
    @4
    @22
    @14
    @16
    @19
    @20
    @6
    @21
    @22
    @23
    simprd
    @8
    @1
    @4
    w3a
    @22
    @14
    @7
    cB
    cY
    dvdsmultr1
    imp
    syl31anc
    @8
    @10
    @12
    w3a
    @13
    @14
    wa
    @15
    @7
    @9
    @11
    dvds2add
    imp
    syl32anc
end
