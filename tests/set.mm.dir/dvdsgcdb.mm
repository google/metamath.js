include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "dvdsgcd.mm"
include "gcddvds.mm"
include "simpld.mm"
include "3adant1.mm"
include "wi.mm"
include "simp1.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "simp2.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "simprd.mm"
include "syld3an2.mm"
include "jcad.mm"
include "impbid.mm"

theorem dvdsgcdb
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K || M /\ K || N ) <-> K || ( M gcd N ) ) )

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
    cdvds
    wbr
    #
    cK
    cN
    cdvds
    wbr
    #
    wa
    cK
    cM
    cN
    cgcd
    co
    #
    cdvds
    wbr
    #
    cK
    cM
    cN
    dvdsgcd
    @3
    @7
    @4
    @5
    @3
    @7
    @6
    cM
    cdvds
    wbr
    #
    @4
    @1
    @2
    @8
    @0
    @1
    @2
    wa
    #
    @8
    @6
    cN
    cdvds
    wbr
    #
    cM
    cN
    gcddvds
    #
    simpld
    3adant1
    @3
    @0
    @6
    cz
    wcel
    #
    @1
    @7
    @8
    wa
    @4
    wi
    @0
    @1
    @2
    simp1
    @1
    @2
    @12
    @0
    @9
    @6
    cM
    cN
    gcdcl
    nn0zd
    3adant1
    #
    @0
    @1
    @2
    simp2
    cK
    @6
    cM
    dvdstr
    syl3anc
    mpan2d
    @3
    @7
    @10
    @5
    @1
    @2
    @10
    @0
    @9
    @8
    @10
    @11
    simprd
    3adant1
    @0
    @12
    @1
    @2
    @7
    @10
    wa
    @5
    wi
    @13
    cK
    @6
    cN
    dvdstr
    syld3an2
    mpan2d
    jcad
    impbid
end
