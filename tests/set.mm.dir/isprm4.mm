include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cn.mm"
include "wral.mm"
include "wa.mm"
include "isprm2.mm"
include "wne.mm"
include "eluz2b3.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bi2.04.mm"
include "wn.mm"
include "df-ne.mm"
include "df-or.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "ralbii2.mm"
include "anbi2i.mm"

theorem isprm4
  let vz: setvar z
  let cP: class P
  let vn: setvar n

  disjoint P z
  disjoint n z
  disjoint P n
  assert |- ( P e. Prime <-> ( P e. ( ZZ>= ` 2 ) /\ A. z e. ( ZZ>= ` 2 ) ( z || P -> z = P ) ) )

  proof
    cP
    cprime
    wcel
    cP
    c2
    cuz
    cfv
    #
    wcel
    #
    vz
    cv
    #
    cP
    cdvds
    wbr
    #
    @2
    c1
    wceq
    #
    @2
    cP
    wceq
    #
    wo
    #
    wi
    #
    vz
    cn
    wral
    #
    wa
    @1
    @3
    @5
    wi
    #
    vz
    @0
    wral
    #
    wa
    vz
    cP
    isprm2
    @10
    @8
    @1
    @9
    @7
    vz
    @0
    cn
    @2
    @0
    wcel
    #
    @9
    wi
    @2
    cn
    wcel
    #
    @2
    c1
    wne
    #
    wa
    #
    @9
    wi
    #
    @12
    @7
    wi
    #
    @11
    @14
    @9
    @2
    eluz2b3
    imbi1i
    @15
    @12
    @13
    @9
    wi
    #
    wi
    @16
    @12
    @13
    @9
    impexp
    @17
    @7
    @12
    @17
    @3
    @13
    @5
    wi
    #
    wi
    @7
    @13
    @3
    @5
    bi2.04
    @18
    @6
    @3
    @18
    @4
    wn
    #
    @5
    wi
    @6
    @13
    @19
    @5
    @2
    c1
    df-ne
    imbi1i
    @4
    @5
    df-or
    bitr4i
    imbi2i
    bitri
    imbi2i
    bitri
    bitri
    ralbii2
    anbi2i
    bitr4i
end
