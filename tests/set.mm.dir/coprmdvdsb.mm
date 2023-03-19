include "cz.mm"
include "wcel.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "wi.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp2.mm"
include "dvdsmultr2.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "coprmdvds.mm"
include "mpan2d.mm"
include "impbid.mm"

theorem coprmdvdsb
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ N e. ZZ /\ ( M e. ZZ /\ ( K gcd M ) = 1 ) ) -> ( K || N <-> K || ( M x. N ) ) )

  proof
    cK
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cK
    cM
    cgcd
    co
    c1
    wceq
    #
    wa
    #
    w3a
    #
    cK
    cN
    cdvds
    wbr
    #
    cK
    cM
    cN
    cmul
    co
    cdvds
    wbr
    #
    @5
    @0
    @2
    @1
    @6
    @7
    wi
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @2
    @3
    simp3l
    #
    @0
    @1
    @4
    simp2
    #
    cK
    cM
    cN
    dvdsmultr2
    syl3anc
    @5
    @7
    @3
    @6
    @0
    @1
    @2
    @3
    simp3r
    @5
    @0
    @2
    @1
    @7
    @3
    wa
    @6
    wi
    @8
    @9
    @10
    cK
    cM
    cN
    coprmdvds
    syl3anc
    mpan2d
    impbid
end
