include "cgz.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cc.mm"
include "cre.mm"
include "cfv.mm"
include "cz.mm"
include "cim.mm"
include "gzcn.mm"
include "addcl.mm"
include "syl2an.mm"
include "wceq.mm"
include "readd.mm"
include "elgz.mm"
include "simp2bi.mm"
include "zaddcl.mm"
include "eqeltrd.mm"
include "imadd.mm"
include "simp3bi.mm"
include "syl3anbrc.mm"

theorem gzaddcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Z[i] /\ B e. Z[i] ) -> ( A + B ) e. Z[i] )

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
    caddc
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
    addcl
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
    caddc
    co
    #
    cz
    @0
    @7
    @8
    @5
    @13
    wceq
    @1
    @9
    @10
    cA
    cB
    readd
    syl2an
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
    @14
    cA
    cim
    cfv
    #
    cz
    wcel
    #
    cA
    elgz
    #
    simp2bi
    @1
    @8
    @15
    cB
    cim
    cfv
    #
    cz
    wcel
    #
    cB
    elgz
    #
    simp2bi
    @11
    @12
    zaddcl
    syl2an
    eqeltrd
    @2
    @6
    @16
    @19
    caddc
    co
    #
    cz
    @0
    @7
    @8
    @6
    @22
    wceq
    @1
    @9
    @10
    cA
    cB
    imadd
    syl2an
    @0
    @17
    @20
    @22
    cz
    wcel
    @1
    @0
    @7
    @14
    @17
    @18
    simp3bi
    @1
    @8
    @15
    @20
    @21
    simp3bi
    @16
    @19
    zaddcl
    syl2an
    eqeltrd
    @3
    elgz
    syl3anbrc
end
