include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "wb.mm"
include "coprm.mm"
include "3adant3.mm"
include "anbi2d.mm"
include "prmz.mm"
include "coprmdvds.mm"
include "syl3an1.mm"
include "sylbid.mm"
include "expd.mm"
include "df-or.mm"
include "syl6ibr.mm"
include "ordvdsmul.mm"
include "impbid.mm"

theorem euclemma
  let cP: class P
  let cM: class M
  let cN: class N


  assert |- ( ( P e. Prime /\ M e. ZZ /\ N e. ZZ ) -> ( P || ( M x. N ) <-> ( P || M \/ P || N ) ) )

  proof
    cP
    cprime
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
    cP
    cM
    cN
    cmul
    co
    cdvds
    wbr
    #
    cP
    cM
    cdvds
    wbr
    #
    cP
    cN
    cdvds
    wbr
    #
    wo
    #
    @3
    @4
    @5
    wn
    #
    @6
    wi
    @7
    @3
    @4
    @8
    @6
    @3
    @4
    @8
    wa
    @4
    cP
    cM
    cgcd
    co
    c1
    wceq
    #
    wa
    #
    @6
    @3
    @8
    @9
    @4
    @0
    @1
    @8
    @9
    wb
    @2
    cP
    cM
    coprm
    3adant3
    anbi2d
    @0
    cP
    cz
    wcel
    #
    @1
    @2
    @10
    @6
    wi
    cP
    prmz
    #
    cP
    cM
    cN
    coprmdvds
    syl3an1
    sylbid
    expd
    @5
    @6
    df-or
    syl6ibr
    @0
    @11
    @1
    @2
    @7
    @4
    wi
    @12
    cP
    cM
    cN
    ordvdsmul
    syl3an1
    impbid
end
