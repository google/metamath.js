include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "c3.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "cfv.mm"
include "clt.mm"
include "eldifi.mm"
include "oddprmgt2.mm"
include "wa.mm"
include "3z.mm"
include "a1i.mm"
include "prmz.mm"
include "adantr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "df-3.mm"
include "wb.mm"
include "2z.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "biimpa.mm"
include "syl5eqbr.mm"
include "3jca.mm"
include "syl2anc.mm"
include "eluz2.mm"
include "sylibr.mm"

theorem oddprmge3
  let cP: class P


  assert |- ( P e. ( Prime \ { 2 } ) -> P e. ( ZZ>= ` 3 ) )

  proof
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    c3
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    c3
    cP
    cle
    wbr
    #
    w3a
    #
    cP
    c3
    cuz
    cfv
    wcel
    @1
    cP
    cprime
    wcel
    #
    c2
    cP
    clt
    wbr
    #
    @5
    cP
    cprime
    @0
    eldifi
    cP
    oddprmgt2
    @6
    @7
    wa
    #
    @2
    @3
    @4
    @2
    @8
    3z
    a1i
    @6
    @3
    @7
    cP
    prmz
    #
    adantr
    @8
    c3
    c2
    c1
    caddc
    co
    #
    cP
    cle
    df-3
    @6
    @7
    @10
    cP
    cle
    wbr
    #
    @6
    c2
    cz
    wcel
    @3
    @7
    @11
    wb
    2z
    @9
    c2
    cP
    zltp1le
    sylancr
    biimpa
    syl5eqbr
    3jca
    syl2anc
    c3
    cP
    eluz2
    sylibr
end
