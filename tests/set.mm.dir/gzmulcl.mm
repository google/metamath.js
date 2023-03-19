include "cgz.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cc.mm"
include "cre.mm"
include "cfv.mm"
include "cz.mm"
include "cim.mm"
include "gzcn.mm"
include "mulcl.mm"
include "syl2an.mm"
include "cmin.mm"
include "wceq.mm"
include "remul.mm"
include "elgz.mm"
include "simp2bi.mm"
include "zmulcl.mm"
include "simp3bi.mm"
include "zsubcld.mm"
include "eqeltrd.mm"
include "caddc.mm"
include "immul.mm"
include "zaddcld.mm"
include "syl3anbrc.mm"

theorem gzmulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Z[i] /\ B e. Z[i] ) -> ( A x. B ) e. Z[i] )

  proof
    cA
    cgz
    wcel
    #
    cB
    cgz
    wcel
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    cc
    wcel
    #
    @3
    cre
    cfv
    #
    cz
    wcel
    @3
    cim
    cfv
    #
    cz
    wcel
    @3
    cgz
    wcel
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @4
    @1
    cA
    gzcn
    #
    cB
    gzcn
    #
    cA
    cB
    mulcl
    syl2an
    @2
    @5
    cA
    cre
    cfv
    #
    cB
    cre
    cfv
    #
    cmul
    co
    #
    cA
    cim
    cfv
    #
    cB
    cim
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cz
    @0
    @7
    @8
    @5
    @17
    wceq
    @1
    @9
    @10
    cA
    cB
    remul
    syl2an
    @2
    @13
    @16
    @0
    @11
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    @13
    cz
    wcel
    @1
    @0
    @7
    @18
    @14
    cz
    wcel
    #
    cA
    elgz
    #
    simp2bi
    #
    @1
    @8
    @19
    @15
    cz
    wcel
    #
    cB
    elgz
    #
    simp2bi
    #
    @11
    @12
    zmulcl
    syl2an
    @0
    @20
    @23
    @16
    cz
    wcel
    @1
    @0
    @7
    @18
    @20
    @21
    simp3bi
    #
    @1
    @8
    @19
    @23
    @24
    simp3bi
    #
    @14
    @15
    zmulcl
    syl2an
    zsubcld
    eqeltrd
    @2
    @6
    @11
    @15
    cmul
    co
    #
    @14
    @12
    cmul
    co
    #
    caddc
    co
    #
    cz
    @0
    @7
    @8
    @6
    @30
    wceq
    @1
    @9
    @10
    cA
    cB
    immul
    syl2an
    @2
    @28
    @29
    @0
    @18
    @23
    @28
    cz
    wcel
    @1
    @22
    @27
    @11
    @15
    zmulcl
    syl2an
    @0
    @20
    @19
    @29
    cz
    wcel
    @1
    @26
    @25
    @14
    @12
    zmulcl
    syl2an
    zaddcld
    eqeltrd
    @3
    elgz
    syl3anbrc
end
