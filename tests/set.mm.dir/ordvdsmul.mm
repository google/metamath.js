include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "dvdsmultr1.mm"
include "dvdsmultr2.mm"
include "jaod.mm"

theorem ordvdsmul
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K || M \/ K || N ) -> K || ( M x. N ) ) )

  proof
    cK
    cz
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    w3a
    cK
    cM
    cdvds
    wbr
    cK
    cM
    cN
    cmul
    co
    cdvds
    wbr
    cK
    cN
    cdvds
    wbr
    cK
    cM
    cN
    dvdsmultr1
    cK
    cM
    cN
    dvdsmultr2
    jaod
end
