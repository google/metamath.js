include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "clcm.mm"
include "co.mm"
include "lcmdvds.mm"
include "dvdslcm.mm"
include "simpld.mm"
include "3adant1.mm"
include "wi.mm"
include "simp2.mm"
include "lcmcl.mm"
include "nn0zd.mm"
include "simp1.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "simprd.mm"
include "3com13.mm"
include "syld3an2.mm"
include "jcad.mm"
include "impbid.mm"

theorem lcmdvdsb
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( M || K /\ N || K ) <-> ( M lcm N ) || K ) )

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
    cK
    cdvds
    wbr
    #
    cN
    cK
    cdvds
    wbr
    #
    wa
    cM
    cN
    clcm
    co
    #
    cK
    cdvds
    wbr
    #
    cK
    cM
    cN
    lcmdvds
    @3
    @7
    @4
    @5
    @3
    cM
    @6
    cdvds
    wbr
    #
    @7
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
    cN
    @6
    cdvds
    wbr
    #
    cM
    cN
    dvdslcm
    #
    simpld
    3adant1
    @3
    @1
    @6
    cz
    wcel
    #
    @0
    @8
    @7
    wa
    @4
    wi
    @0
    @1
    @2
    simp2
    @1
    @2
    @12
    @0
    @9
    @6
    cM
    cN
    lcmcl
    nn0zd
    3adant1
    #
    @0
    @1
    @2
    simp1
    cM
    @6
    cK
    dvdstr
    syl3anc
    mpand
    @3
    @10
    @7
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
    @10
    @7
    wa
    @5
    wi
    #
    @13
    @2
    @12
    @0
    @14
    cN
    @6
    cK
    dvdstr
    3com13
    syld3an2
    mpand
    jcad
    impbid
end
