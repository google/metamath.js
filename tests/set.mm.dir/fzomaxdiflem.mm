include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "cr.mm"
include "wceq.mm"
include "cz.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "adantr.mm"
include "zsubcld.mm"
include "zred.mm"
include "subge0d.mm"
include "biimpar.mm"
include "absid.mm"
include "syl2anc.mm"
include "clt.mm"
include "elfzoel1.mm"
include "resubcld.mm"
include "elfzoel2.mm"
include "elfzole1.mm"
include "lesub2dd.mm"
include "elfzolt2.mm"
include "ltsub1dd.mm"
include "lelttrd.mm"
include "wb.mm"
include "0zd.mm"
include "elfzo.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"

theorem fzomaxdiflem
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ( C ..^ D ) /\ B e. ( C ..^ D ) ) /\ A <_ B ) -> ( abs ` ( B - A ) ) e. ( 0 ..^ ( D - C ) ) )

  proof
    cA
    cC
    cD
    cfzo
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    wa
    #
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    cc0
    cD
    cC
    cmin
    co
    #
    cfzo
    co
    #
    @5
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @7
    @6
    wceq
    @3
    @10
    @4
    @3
    @6
    @3
    cB
    cA
    @2
    cB
    cz
    wcel
    @1
    cB
    cC
    cD
    elfzoelz
    adantl
    #
    @1
    cA
    cz
    wcel
    @2
    cA
    cC
    cD
    elfzoelz
    adantr
    #
    zsubcld
    #
    zred
    #
    adantr
    @3
    @11
    @4
    @3
    cB
    cA
    @3
    cB
    @12
    zred
    #
    @3
    cA
    @13
    zred
    #
    subge0d
    biimpar
    #
    @6
    absid
    syl2anc
    @5
    @6
    @9
    wcel
    #
    @11
    @6
    @8
    clt
    wbr
    #
    @18
    @3
    @20
    @4
    @3
    @6
    cB
    cC
    cmin
    co
    @8
    @15
    @3
    cB
    cC
    @16
    @3
    cC
    @2
    cC
    cz
    wcel
    @1
    cB
    cC
    cD
    elfzoel1
    adantl
    #
    zred
    #
    resubcld
    @3
    @8
    @3
    cD
    cC
    @2
    cD
    cz
    wcel
    @1
    cB
    cC
    cD
    elfzoel2
    adantl
    #
    @21
    zsubcld
    #
    zred
    @3
    cC
    cA
    cB
    @22
    @17
    @16
    @1
    cC
    cA
    cle
    wbr
    @2
    cA
    cC
    cD
    elfzole1
    adantr
    lesub2dd
    @3
    cB
    cD
    cC
    @16
    @3
    cD
    @23
    zred
    @22
    @2
    cB
    cD
    clt
    wbr
    @1
    cB
    cC
    cD
    elfzolt2
    adantl
    ltsub1dd
    lelttrd
    adantr
    @3
    @19
    @11
    @20
    wa
    wb
    #
    @4
    @3
    @6
    cz
    wcel
    cc0
    cz
    wcel
    @8
    cz
    wcel
    @25
    @14
    @3
    0zd
    @24
    @6
    cc0
    @8
    elfzo
    syl3anc
    adantr
    mpbir2and
    eqeltrd
end
