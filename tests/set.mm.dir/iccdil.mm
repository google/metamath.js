include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cicc.mm"
include "wb.mm"
include "simpl.mm"
include "rpre.mm"
include "remulcl.mm"
include "sylan2.mm"
include "2thd.mm"
include "adantl.mm"
include "cc0.mm"
include "clt.mm"
include "elrp.mm"
include "lemul1.mm"
include "syl3an3b.mm"
include "3expb.mm"
include "adantlr.mm"
include "breq1i.mm"
include "syl6bb.mm"
include "an12s.mm"
include "adantll.mm"
include "breq2i.mm"
include "3anbi123d.mm"
include "elicc2.mm"
include "adantr.mm"
include "syl5eqelr.mm"
include "syl2an.mm"
include "anandirs.mm"
include "adantrl.mm"
include "3bitr4d.mm"

theorem iccdil
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  assume iccdil.1: |- ( A x. R ) = C
  assume iccdil.2: |- ( B x. R ) = D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( X e. RR /\ R e. RR+ ) ) -> ( X e. ( A [,] B ) <-> ( X x. R ) e. ( C [,] D ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cX
    cr
    wcel
    #
    cR
    crp
    wcel
    #
    wa
    #
    wa
    #
    @3
    cA
    cX
    cle
    wbr
    #
    cX
    cB
    cle
    wbr
    #
    w3a
    #
    cX
    cR
    cmul
    co
    #
    cr
    wcel
    #
    cC
    @10
    cle
    wbr
    #
    @10
    cD
    cle
    wbr
    #
    w3a
    #
    cX
    cA
    cB
    cicc
    co
    wcel
    #
    @10
    cC
    cD
    cicc
    co
    wcel
    #
    @6
    @3
    @11
    @7
    @12
    @8
    @13
    @5
    @3
    @11
    wb
    @2
    @5
    @3
    @11
    @3
    @4
    simpl
    @4
    @3
    cR
    cr
    wcel
    #
    @11
    cR
    rpre
    #
    cX
    cR
    remulcl
    sylan2
    2thd
    adantl
    @6
    @7
    cA
    cR
    cmul
    co
    #
    @10
    cle
    wbr
    #
    @12
    @0
    @5
    @7
    @20
    wb
    #
    @1
    @0
    @3
    @4
    @21
    @4
    @0
    @3
    @17
    cc0
    cR
    clt
    wbr
    wa
    #
    @21
    cR
    elrp
    #
    cA
    cX
    cR
    lemul1
    syl3an3b
    3expb
    adantlr
    @19
    cC
    @10
    cle
    iccdil.1
    breq1i
    syl6bb
    @6
    @8
    @10
    cB
    cR
    cmul
    co
    #
    cle
    wbr
    #
    @13
    @1
    @5
    @8
    @25
    wb
    #
    @0
    @3
    @1
    @4
    @26
    @3
    @1
    @4
    @26
    @4
    @3
    @1
    @22
    @26
    @23
    cX
    cB
    cR
    lemul1
    syl3an3b
    3expb
    an12s
    adantll
    @24
    cD
    @10
    cle
    iccdil.2
    breq2i
    syl6bb
    3anbi123d
    @2
    @15
    @9
    wb
    @5
    cA
    cB
    cX
    elicc2
    adantr
    @2
    @4
    @16
    @14
    wb
    #
    @3
    @4
    @2
    @17
    @27
    @18
    @0
    @1
    @17
    @27
    @0
    @17
    wa
    #
    cC
    cr
    wcel
    cD
    cr
    wcel
    @27
    @1
    @17
    wa
    #
    @28
    cC
    @19
    cr
    iccdil.1
    cA
    cR
    remulcl
    syl5eqelr
    @29
    cD
    @24
    cr
    iccdil.2
    cB
    cR
    remulcl
    syl5eqelr
    cC
    cD
    @10
    elicc2
    syl2an
    anandirs
    sylan2
    adantrl
    3bitr4d
end
