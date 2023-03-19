include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "id.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "0z.mm"
include "elimel.mm"
include "gcdaddmlem.mm"
include "dedth3h.mm"
include "wa.mm"
include "cc.mm"
include "zcn.mm"
include "mulcl.mm"
include "syl2an.mm"
include "addcom.mm"
include "3impa.mm"
include "eqtrd.mm"

theorem gcdaddm
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( M gcd N ) = ( M gcd ( N + ( K x. M ) ) ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cM
    cN
    cgcd
    co
    #
    cM
    cK
    cM
    cmul
    co
    #
    cN
    caddc
    co
    #
    cgcd
    co
    #
    cM
    cN
    @5
    caddc
    co
    #
    cgcd
    co
    @0
    @1
    @2
    @4
    @7
    wceq
    @4
    cM
    @0
    cK
    cc0
    cif
    #
    cM
    cmul
    co
    #
    cN
    caddc
    co
    #
    cgcd
    co
    #
    wceq
    @1
    cM
    cc0
    cif
    #
    cN
    cgcd
    co
    #
    @13
    @9
    @13
    cmul
    co
    #
    cN
    caddc
    co
    #
    cgcd
    co
    #
    wceq
    @13
    @2
    cN
    cc0
    cif
    #
    cgcd
    co
    #
    @13
    @15
    @18
    caddc
    co
    #
    cgcd
    co
    #
    wceq
    cK
    cM
    cN
    cc0
    cc0
    cc0
    cK
    @9
    wceq
    #
    @7
    @12
    @4
    @22
    @6
    @11
    cM
    cgcd
    @22
    @5
    @10
    cN
    caddc
    cK
    @9
    cM
    cmul
    oveq1
    oveq1d
    oveq2d
    eqeq2d
    cM
    @13
    wceq
    #
    @4
    @14
    @12
    @17
    cM
    @13
    cN
    cgcd
    oveq1
    @23
    cM
    @13
    @11
    @16
    cgcd
    @23
    id
    @23
    @10
    @15
    cN
    caddc
    cM
    @13
    @9
    cmul
    oveq2
    oveq1d
    oveq12d
    eqeq12d
    cN
    @18
    wceq
    #
    @14
    @19
    @17
    @21
    cN
    @18
    @13
    cgcd
    oveq2
    @24
    @16
    @20
    @13
    cgcd
    cN
    @18
    @15
    caddc
    oveq2
    oveq2d
    eqeq12d
    @9
    @13
    @18
    cK
    cc0
    cz
    0z
    elimel
    cM
    cc0
    cz
    0z
    elimel
    cN
    cc0
    cz
    0z
    elimel
    gcdaddmlem
    dedth3h
    @3
    @6
    @8
    cM
    cgcd
    @0
    @1
    @2
    @6
    @8
    wceq
    #
    @0
    @1
    wa
    @5
    cc
    wcel
    #
    cN
    cc
    wcel
    @25
    @2
    @0
    cK
    cc
    wcel
    cM
    cc
    wcel
    @26
    @1
    cK
    zcn
    cM
    zcn
    cK
    cM
    mulcl
    syl2an
    cN
    zcn
    @5
    cN
    addcom
    syl2an
    3impa
    oveq2d
    eqtrd
end
