include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "wb.mm"
include "dvdsmul2.mm"
include "biantrud.mm"
include "3adant1.mm"
include "wi.mm"
include "simp1.mm"
include "simp3.mm"
include "zmulcl.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "sylbid.mm"

theorem dvdsmultr2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( K || N -> K || ( M x. N ) ) )

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
    cN
    cdvds
    wbr
    #
    @4
    cN
    cM
    cN
    cmul
    co
    #
    cdvds
    wbr
    #
    wa
    #
    cK
    @5
    cdvds
    wbr
    #
    @1
    @2
    @4
    @7
    wb
    @0
    @1
    @2
    wa
    @6
    @4
    cM
    cN
    dvdsmul2
    biantrud
    3adant1
    @3
    @0
    @2
    @5
    cz
    wcel
    #
    @7
    @8
    wi
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @1
    @2
    @9
    @0
    cM
    cN
    zmulcl
    3adant1
    cK
    cN
    @5
    dvdstr
    syl3anc
    sylbid
end
