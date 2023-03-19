include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cva.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "normcl.mm"
include "resqcld.mm"
include "recnd.mm"
include "addid1d.mm"
include "adantr.mm"
include "sqge0d.mm"
include "adantl.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "leadd2.mm"
include "mp3an1.mm"
include "syl2anr.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "normpyth.mm"
include "imp.mm"
include "breqtrrd.mm"
include "ex.mm"
include "hvaddcl.mm"
include "syl.mm"
include "normge0.mm"
include "le2sqd.mm"
include "sylibrd.mm"

theorem normpyc
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A .ih B ) = 0 -> ( normh ` A ) <_ ( normh ` ( A +h B ) ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cB
    csp
    co
    cc0
    wceq
    #
    cA
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cB
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @4
    @7
    cle
    wbr
    @2
    @3
    @9
    @2
    @3
    wa
    @5
    @5
    cB
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @8
    cle
    @2
    @5
    @12
    cle
    wbr
    @3
    @2
    @5
    cc0
    caddc
    co
    #
    @5
    @12
    cle
    @0
    @13
    @5
    wceq
    @1
    @0
    @5
    @0
    @5
    @0
    @4
    cA
    normcl
    #
    resqcld
    #
    recnd
    addid1d
    adantr
    @2
    cc0
    @11
    cle
    wbr
    #
    @13
    @12
    cle
    wbr
    #
    @1
    @16
    @0
    @1
    @10
    cB
    normcl
    #
    sqge0d
    adantl
    @1
    @11
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @16
    @17
    wb
    #
    @0
    @1
    @10
    @18
    resqcld
    @15
    cc0
    cr
    wcel
    @19
    @20
    @21
    0re
    cc0
    @11
    @5
    leadd2
    mp3an1
    syl2anr
    mpbid
    eqbrtrrd
    adantr
    @2
    @3
    @8
    @12
    wceq
    cA
    cB
    normpyth
    imp
    breqtrrd
    ex
    @2
    @4
    @7
    @0
    @4
    cr
    wcel
    @1
    @14
    adantr
    @2
    @6
    chil
    wcel
    #
    @7
    cr
    wcel
    cA
    cB
    hvaddcl
    #
    @6
    normcl
    syl
    @0
    cc0
    @4
    cle
    wbr
    @1
    cA
    normge0
    adantr
    @2
    @22
    cc0
    @7
    cle
    wbr
    @23
    @6
    normge0
    syl
    le2sqd
    sylibrd
end
