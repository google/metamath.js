include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "wo.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cr.mm"
include "zre.mm"
include "adantl.mm"
include "elfzoelz.mm"
include "adantr.mm"
include "zred.mm"
include "lelttric.mm"
include "syl2anc.mm"
include "orcomd.mm"
include "elfzole1.mm"
include "a1d.mm"
include "ancrd.mm"
include "elfzolt2.mm"
include "ancld.mm"
include "orim12d.mm"
include "mpd.mm"
include "wb.mm"
include "elfzoel1.mm"
include "simpr.mm"
include "elfzo.mm"
include "syl3anc.mm"
include "elfzoel2.mm"
include "orbi12d.mm"
include "mpbird.mm"

theorem fzospliti
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( B ..^ C ) /\ D e. ZZ ) -> ( A e. ( B ..^ D ) \/ A e. ( D ..^ C ) ) )

  proof
    cA
    cB
    cC
    cfzo
    co
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cD
    cfzo
    co
    wcel
    #
    cA
    cD
    cC
    cfzo
    co
    wcel
    #
    wo
    cB
    cA
    cle
    wbr
    #
    cA
    cD
    clt
    wbr
    #
    wa
    #
    cD
    cA
    cle
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    wa
    #
    wo
    #
    @2
    @6
    @8
    wo
    @11
    @2
    @8
    @6
    @2
    cD
    cr
    wcel
    #
    cA
    cr
    wcel
    @8
    @6
    wo
    @1
    @12
    @0
    cD
    zre
    adantl
    @2
    cA
    @0
    cA
    cz
    wcel
    #
    @1
    cA
    cB
    cC
    elfzoelz
    adantr
    #
    zred
    cD
    cA
    lelttric
    syl2anc
    orcomd
    @2
    @6
    @7
    @8
    @10
    @2
    @6
    @5
    @2
    @5
    @6
    @0
    @5
    @1
    cA
    cB
    cC
    elfzole1
    adantr
    a1d
    ancrd
    @2
    @8
    @9
    @2
    @9
    @8
    @0
    @9
    @1
    cA
    cB
    cC
    elfzolt2
    adantr
    a1d
    ancld
    orim12d
    mpd
    @2
    @3
    @7
    @4
    @10
    @2
    @13
    cB
    cz
    wcel
    #
    @1
    @3
    @7
    wb
    @14
    @0
    @15
    @1
    cA
    cB
    cC
    elfzoel1
    adantr
    @0
    @1
    simpr
    #
    cA
    cB
    cD
    elfzo
    syl3anc
    @2
    @13
    @1
    cC
    cz
    wcel
    #
    @4
    @10
    wb
    @14
    @16
    @0
    @17
    @1
    cA
    cB
    cC
    elfzoel2
    adantr
    cA
    cD
    cC
    elfzo
    syl3anc
    orbi12d
    mpbird
end
