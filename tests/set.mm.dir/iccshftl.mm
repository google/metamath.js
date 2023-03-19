include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "wb.mm"
include "simpl.mm"
include "resubcl.mm"
include "2thd.mm"
include "adantl.mm"
include "lesub1.mm"
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

theorem iccshftl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  assume iccshftl.1: |- ( A - R ) = C
  assume iccshftl.2: |- ( B - R ) = D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( X e. RR /\ R e. RR ) ) -> ( X e. ( A [,] B ) <-> ( X - R ) e. ( C [,] D ) ) )

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
    cr
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
    cmin
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
    cX
    cR
    resubcl
    2thd
    adantl
    @6
    @7
    cA
    cR
    cmin
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
    @18
    wb
    #
    @1
    @0
    @3
    @4
    @19
    cA
    cX
    cR
    lesub1
    3expb
    adantlr
    @17
    cC
    @10
    cle
    iccshftl.1
    breq1i
    syl6bb
    @6
    @8
    @10
    cB
    cR
    cmin
    co
    #
    cle
    wbr
    #
    @13
    @1
    @5
    @8
    @21
    wb
    #
    @0
    @3
    @1
    @4
    @22
    @3
    @1
    @4
    @22
    cX
    cB
    cR
    lesub1
    3expb
    an12s
    adantll
    @20
    cD
    @10
    cle
    iccshftl.2
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
    @0
    @1
    @4
    @23
    @0
    @4
    wa
    #
    cC
    cr
    wcel
    cD
    cr
    wcel
    @23
    @1
    @4
    wa
    #
    @24
    cC
    @17
    cr
    iccshftl.1
    cA
    cR
    resubcl
    syl5eqelr
    @25
    cD
    @20
    cr
    iccshftl.2
    cB
    cR
    resubcl
    syl5eqelr
    cC
    cD
    @10
    elicc2
    syl2an
    anandirs
    adantrl
    3bitr4d
end
