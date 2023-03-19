include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "dvdsmul1.mm"
include "3adant1.mm"
include "wa.mm"
include "wi.mm"
include "zmulcl.mm"
include "dvdstr.mm"
include "syld3an3.mm"
include "mpan2d.mm"

theorem dvdsmultr1
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( K || M -> K || ( M x. N ) ) )

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
    cK
    cM
    cdvds
    wbr
    #
    cM
    cM
    cN
    cmul
    co
    #
    cdvds
    wbr
    #
    cK
    @4
    cdvds
    wbr
    #
    @1
    @2
    @5
    @0
    cM
    cN
    dvdsmul1
    3adant1
    @0
    @1
    @2
    @4
    cz
    wcel
    #
    @3
    @5
    wa
    @6
    wi
    @1
    @2
    @7
    @0
    cM
    cN
    zmulcl
    3adant1
    cK
    cM
    @4
    dvdstr
    syld3an3
    mpan2d
end
