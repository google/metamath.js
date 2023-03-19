include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "resqcl.mm"
include "sqge0.mm"
include "absid.mm"
include "syl2anc.mm"
include "cc.mm"
include "cn0.mm"
include "recn.mm"
include "2nn0.mm"
include "absexp.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "eqeqan12d.mm"
include "wb.mm"
include "abscl.mm"
include "absge0.mm"
include "jca.mm"
include "sq11.mm"
include "syl2an.mm"
include "bitrd.mm"

theorem sqabs
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( A ^ 2 ) = ( B ^ 2 ) <-> ( abs ` A ) = ( abs ` B ) ) )

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
    wceq
    cA
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cB
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    @4
    @6
    wceq
    #
    @0
    @1
    @2
    @5
    @3
    @7
    @0
    @2
    cabs
    cfv
    #
    @2
    @5
    @0
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    @10
    @2
    wceq
    cA
    resqcl
    cA
    sqge0
    @2
    absid
    syl2anc
    @0
    cA
    cc
    wcel
    #
    c2
    cn0
    wcel
    #
    @10
    @5
    wceq
    cA
    recn
    #
    2nn0
    cA
    c2
    absexp
    sylancl
    eqtr3d
    @1
    @3
    cabs
    cfv
    #
    @3
    @7
    @1
    @3
    cr
    wcel
    cc0
    @3
    cle
    wbr
    @14
    @3
    wceq
    cB
    resqcl
    cB
    sqge0
    @3
    absid
    syl2anc
    @1
    cB
    cc
    wcel
    #
    @12
    @14
    @7
    wceq
    cB
    recn
    #
    2nn0
    cB
    c2
    absexp
    sylancl
    eqtr3d
    eqeqan12d
    @0
    @11
    @15
    @8
    @9
    wb
    #
    @1
    @13
    @16
    @11
    @4
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    wa
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    wa
    @17
    @15
    @11
    @18
    @19
    cA
    abscl
    cA
    absge0
    jca
    @15
    @20
    @21
    cB
    abscl
    cB
    absge0
    jca
    @4
    @6
    sq11
    syl2an
    syl2an
    bitrd
end
