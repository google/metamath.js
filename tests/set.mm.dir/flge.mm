include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "flltp1.mm"
include "adantr.mm"
include "wi.mm"
include "simpr.mm"
include "zred.mm"
include "simpl.mm"
include "flcld.mm"
include "peano2zd.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "wb.mm"
include "zleltp1.mm"
include "syl2anc.mm"
include "sylibrd.mm"
include "flle.mm"
include "letr.mm"
include "impbid.mm"

theorem flge
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. ZZ ) -> ( B <_ A <-> B <_ ( |_ ` A ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cB
    cA
    cle
    wbr
    #
    cB
    cA
    cfl
    cfv
    #
    cle
    wbr
    #
    @2
    @3
    cB
    @4
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @5
    @2
    @3
    cA
    @6
    clt
    wbr
    #
    @7
    @0
    @8
    @1
    cA
    flltp1
    adantr
    @2
    cB
    cr
    wcel
    #
    @0
    @6
    cr
    wcel
    @3
    @8
    wa
    @7
    wi
    @2
    cB
    @0
    @1
    simpr
    #
    zred
    #
    @0
    @1
    simpl
    #
    @2
    @6
    @2
    @4
    @2
    cA
    @12
    flcld
    #
    peano2zd
    zred
    cB
    cA
    @6
    lelttr
    syl3anc
    mpan2d
    @2
    @1
    @4
    cz
    wcel
    @5
    @7
    wb
    @10
    @13
    cB
    @4
    zleltp1
    syl2anc
    sylibrd
    @2
    @5
    @4
    cA
    cle
    wbr
    #
    @3
    @0
    @14
    @1
    cA
    flle
    adantr
    @2
    @9
    @4
    cr
    wcel
    @0
    @5
    @14
    wa
    @3
    wi
    @11
    @2
    @4
    @13
    zred
    @12
    cB
    @4
    cA
    letr
    syl3anc
    mpan2d
    impbid
end
