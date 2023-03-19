include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "coa.mm"
include "co.mm"
include "wss.mm"
include "wb.mm"
include "nnaord.mm"
include "3com12.mm"
include "notbid.mm"
include "word.mm"
include "nnord.mm"
include "ordtri1.mm"
include "syl2an.mm"
include "3adant3.mm"
include "nnacl.mm"
include "ancoms.mm"
include "3adant2.mm"
include "3adant1.mm"
include "syl2anc.mm"
include "3bitr4d.mm"

theorem nnaword
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( A C_ B <-> ( C +o A ) C_ ( C +o B ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
    wcel
    #
    w3a
    #
    cB
    cA
    wcel
    #
    wn
    #
    cC
    cB
    coa
    co
    #
    cC
    cA
    coa
    co
    #
    wcel
    #
    wn
    #
    cA
    cB
    wss
    #
    @7
    @6
    wss
    #
    @3
    @4
    @8
    @1
    @0
    @2
    @4
    @8
    wb
    cB
    cA
    cC
    nnaord
    3com12
    notbid
    @0
    @1
    @10
    @5
    wb
    #
    @2
    @0
    cA
    word
    cB
    word
    @12
    @1
    cA
    nnord
    cB
    nnord
    cA
    cB
    ordtri1
    syl2an
    3adant3
    @3
    @7
    com
    wcel
    #
    @6
    com
    wcel
    #
    @11
    @9
    wb
    #
    @0
    @2
    @13
    @1
    @2
    @0
    @13
    cC
    cA
    nnacl
    ancoms
    3adant2
    @1
    @2
    @14
    @0
    @2
    @1
    @14
    cC
    cB
    nnacl
    ancoms
    3adant1
    @13
    @7
    word
    @6
    word
    @15
    @14
    @7
    nnord
    @6
    nnord
    @7
    @6
    ordtri1
    syl2an
    syl2anc
    3bitr4d
end
