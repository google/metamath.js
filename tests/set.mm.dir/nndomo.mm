include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "wpss.mm"
include "wn.mm"
include "wi.mm"
include "csdm.mm"
include "php2.mm"
include "ex.mm"
include "domnsym.mm"
include "nsyli.mm"
include "adantr.mm"
include "word.mm"
include "wb.mm"
include "nnord.mm"
include "ordtri1.mm"
include "ordelpss.mm"
include "ancoms.mm"
include "notbid.mm"
include "bitrd.mm"
include "syl2an.mm"
include "sylibrd.mm"
include "ssdomg.mm"
include "adantl.mm"
include "impbid.mm"

theorem nndomo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A ~<_ B <-> A C_ B ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    wss
    #
    @2
    @3
    cB
    cA
    wpss
    #
    wn
    #
    @4
    @0
    @3
    @6
    wi
    @1
    @0
    @5
    cB
    cA
    csdm
    wbr
    #
    @3
    @0
    @5
    @7
    cA
    cB
    php2
    ex
    cA
    cB
    domnsym
    nsyli
    adantr
    @0
    cA
    word
    #
    cB
    word
    #
    @4
    @6
    wb
    @1
    cA
    nnord
    cB
    nnord
    @8
    @9
    wa
    #
    @4
    cB
    cA
    wcel
    #
    wn
    @6
    cA
    cB
    ordtri1
    @10
    @11
    @5
    @9
    @8
    @11
    @5
    wb
    cB
    cA
    ordelpss
    ancoms
    notbid
    bitrd
    syl2an
    sylibrd
    @1
    @4
    @3
    wi
    @0
    cA
    cB
    com
    ssdomg
    adantl
    impbid
end
