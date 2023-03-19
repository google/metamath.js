include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "cabs.mm"
include "cfv.mm"
include "cc.mm"
include "recn.mm"
include "abscl.mm"
include "absge0.mm"
include "jca.mm"
include "syl.mm"
include "le2sq.mm"
include "sylan.mm"
include "absle.mm"
include "ancom.mm"
include "lenegcon1.mm"
include "anbi1d.mm"
include "syl5rbbr.mm"
include "bitrd.mm"
include "adantrr.mm"
include "absresq.mm"
include "breq1d.mm"
include "adantr.mm"
include "3bitr3d.mm"
include "3impb.mm"

theorem lenegsq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ 0 <_ B ) -> ( ( A <_ B /\ -u A <_ B ) <-> ( A ^ 2 ) <_ ( B ^ 2 ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cneg
    cB
    cle
    wbr
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cle
    wbr
    #
    wb
    @0
    @1
    @2
    wa
    #
    wa
    cA
    cabs
    cfv
    #
    cB
    cle
    wbr
    #
    @10
    c2
    cexp
    co
    #
    @7
    cle
    wbr
    #
    @5
    @8
    @0
    @10
    cr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    wa
    #
    @9
    @11
    @13
    wb
    @0
    cA
    cc
    wcel
    #
    @16
    cA
    recn
    @17
    @14
    @15
    cA
    abscl
    cA
    absge0
    jca
    syl
    @10
    cB
    le2sq
    sylan
    @0
    @1
    @11
    @5
    wb
    @2
    @0
    @1
    wa
    #
    @11
    cB
    cneg
    cA
    cle
    wbr
    #
    @3
    wa
    #
    @5
    cA
    cB
    absle
    @5
    @4
    @3
    wa
    @18
    @20
    @4
    @3
    ancom
    @18
    @4
    @19
    @3
    cA
    cB
    lenegcon1
    anbi1d
    syl5rbbr
    bitrd
    adantrr
    @0
    @13
    @8
    wb
    @9
    @0
    @12
    @6
    @7
    cle
    cA
    absresq
    breq1d
    adantr
    3bitr3d
    3impb
end
