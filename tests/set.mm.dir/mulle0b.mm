include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wo.mm"
include "remulcl.mm"
include "le0neg1d.mm"
include "wb.mm"
include "le0neg2.mm"
include "anbi2d.mm"
include "le0neg1.mm"
include "orbi12d.mm"
include "adantl.mm"
include "renegcl.mm"
include "mulge0b.mm"
include "sylan2.mm"
include "cc.mm"
include "recn.mm"
include "mulneg2.mm"
include "breq2d.mm"
include "syl2an.mm"
include "3bitr2rd.mm"
include "bitrd.mm"

theorem mulle0b
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( A x. B ) <_ 0 <-> ( ( A <_ 0 /\ 0 <_ B ) \/ ( 0 <_ A /\ B <_ 0 ) ) ) )

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
    cA
    cB
    cmul
    co
    #
    cc0
    cle
    wbr
    cc0
    @3
    cneg
    #
    cle
    wbr
    #
    cA
    cc0
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cB
    cc0
    cle
    wbr
    #
    wa
    #
    wo
    #
    @2
    @3
    cA
    cB
    remulcl
    le0neg1d
    @2
    @12
    @6
    cB
    cneg
    #
    cc0
    cle
    wbr
    #
    wa
    #
    @9
    cc0
    @13
    cle
    wbr
    #
    wa
    #
    wo
    #
    cc0
    cA
    @13
    cmul
    co
    #
    cle
    wbr
    #
    @5
    @1
    @12
    @18
    wb
    @0
    @1
    @8
    @15
    @11
    @17
    @1
    @7
    @14
    @6
    cB
    le0neg2
    anbi2d
    @1
    @10
    @16
    @9
    cB
    le0neg1
    anbi2d
    orbi12d
    adantl
    @1
    @0
    @13
    cr
    wcel
    @20
    @18
    wb
    cB
    renegcl
    cA
    @13
    mulge0b
    sylan2
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @20
    @5
    wb
    @1
    cA
    recn
    cB
    recn
    @21
    @22
    wa
    @19
    @4
    cc0
    cle
    cA
    cB
    mulneg2
    breq2d
    syl2an
    3bitr2rd
    bitrd
end
