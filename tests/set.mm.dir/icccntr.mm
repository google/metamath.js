include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cicc.mm"
include "wb.mm"
include "simpl.mm"
include "rerpdivcl.mm"
include "2thd.mm"
include "adantl.mm"
include "cc0.mm"
include "clt.mm"
include "elrp.mm"
include "lediv1.mm"
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

theorem icccntr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  assume icccntr.1: |- ( A / R ) = C
  assume icccntr.2: |- ( B / R ) = D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( X e. RR /\ R e. RR+ ) ) -> ( X e. ( A [,] B ) <-> ( X / R ) e. ( C [,] D ) ) )

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
    cdiv
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
    rerpdivcl
    2thd
    adantl
    @6
    @7
    cA
    cR
    cdiv
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
    @4
    @0
    @3
    cR
    cr
    wcel
    cc0
    cR
    clt
    wbr
    wa
    #
    @19
    cR
    elrp
    #
    cA
    cX
    cR
    lediv1
    syl3an3b
    3expb
    adantlr
    @17
    cC
    @10
    cle
    icccntr.1
    breq1i
    syl6bb
    @6
    @8
    @10
    cB
    cR
    cdiv
    co
    #
    cle
    wbr
    #
    @13
    @1
    @5
    @8
    @23
    wb
    #
    @0
    @3
    @1
    @4
    @24
    @3
    @1
    @4
    @24
    @4
    @3
    @1
    @20
    @24
    @21
    cX
    cB
    cR
    lediv1
    syl3an3b
    3expb
    an12s
    adantll
    @22
    cD
    @10
    cle
    icccntr.2
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
    @25
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
    @25
    @1
    @4
    wa
    #
    @26
    cC
    @17
    cr
    icccntr.1
    cA
    cR
    rerpdivcl
    syl5eqelr
    @27
    cD
    @22
    cr
    icccntr.2
    cB
    cR
    rerpdivcl
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
