include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "prmuz2.mm"
include "cz.mm"
include "cle.mm"
include "w3a.mm"
include "eluz2.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "df-2.mm"
include "a1i.mm"
include "breq1d.mm"
include "wb.mm"
include "1z.mm"
include "zltp1le.mm"
include "mpan.mm"
include "biimprd.mm"
include "sylbid.mm"
include "imp.mm"
include "3adant1.mm"
include "sylbi.mm"
include "syl.mm"

theorem prmgt1
  let cP: class P


  assert |- ( P e. Prime -> 1 < P )

  proof
    cP
    cprime
    wcel
    cP
    c2
    cuz
    cfv
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    cP
    prmuz2
    @0
    c2
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    c2
    cP
    cle
    wbr
    #
    w3a
    @1
    c2
    cP
    eluz2
    @3
    @4
    @1
    @2
    @3
    @4
    @1
    @3
    @4
    c1
    c1
    caddc
    co
    #
    cP
    cle
    wbr
    #
    @1
    @3
    c2
    @5
    cP
    cle
    c2
    @5
    wceq
    @3
    df-2
    a1i
    breq1d
    @3
    @1
    @6
    c1
    cz
    wcel
    @3
    @1
    @6
    wb
    1z
    c1
    cP
    zltp1le
    mpan
    biimprd
    sylbid
    imp
    3adant1
    sylbi
    syl
end
