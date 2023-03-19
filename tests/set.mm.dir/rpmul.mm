include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "mulgcddvds.mm"
include "oveq12.mm"
include "1t1e1.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "cn0.mm"
include "wb.mm"
include "simp1.mm"
include "zmulcl.mm"
include "3adant1.mm"
include "gcdcld.mm"
include "dvds1.mm"
include "syl.mm"
include "sylibd.mm"

theorem rpmul
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( ( K gcd M ) = 1 /\ ( K gcd N ) = 1 ) -> ( K gcd ( M x. N ) ) = 1 ) )

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
    cK
    cM
    cgcd
    co
    #
    c1
    wceq
    cK
    cN
    cgcd
    co
    #
    c1
    wceq
    wa
    #
    cK
    cM
    cN
    cmul
    co
    #
    cgcd
    co
    #
    c1
    cdvds
    wbr
    #
    @8
    c1
    wceq
    #
    @3
    @8
    @4
    @5
    cmul
    co
    #
    cdvds
    wbr
    @6
    @9
    cK
    cM
    cN
    mulgcddvds
    @6
    @11
    c1
    @8
    cdvds
    @6
    @11
    c1
    c1
    cmul
    co
    c1
    @4
    c1
    @5
    c1
    cmul
    oveq12
    1t1e1
    syl6eq
    breq2d
    syl5ibcom
    @3
    @8
    cn0
    wcel
    @9
    @10
    wb
    @3
    cK
    @7
    @0
    @1
    @2
    simp1
    @1
    @2
    @7
    cz
    wcel
    @0
    cM
    cN
    zmulcl
    3adant1
    gcdcld
    @8
    dvds1
    syl
    sylibd
end
