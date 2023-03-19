include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csm.mm"
include "wceq.mm"
include "c0v.mm"
include "wne.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "chil.mm"
include "hvmulcli.mm"
include "hire.mm"
include "mp2an.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "adantr.mm"
include "eigrei.mm"
include "biimpac.mm"
include "adantlr.mm"
include "clt.mm"
include "cmul.mm"
include "ax-his4.mm"
include "mpan.mm"
include "ad2antll.mm"
include "simplr.mm"
include "ad2antrl.mm"
include "ccj.mm"
include "cc.mm"
include "his5.mm"
include "mp3an.mm"
include "cjred.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "hiidrcl.mm"
include "ax-mp.mm"
include "prodge02.mm"
include "mpanl2.mm"
include "syl12anc.mm"
include "jca.mm"

theorem eigposi
  let cA: class A
  let cB: class B
  let cT: class T
  assume eigpos.1: |- A e. ~H
  assume eigpos.2: |- B e. CC


  assert |- ( ( ( ( A .ih ( T ` A ) ) e. RR /\ 0 <_ ( A .ih ( T ` A ) ) ) /\ ( ( T ` A ) = ( B .h A ) /\ A =/= 0h ) ) -> ( B e. RR /\ 0 <_ B ) )

  proof
    cA
    cA
    cT
    cfv
    #
    csp
    co
    #
    cr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    wa
    #
    @0
    cB
    cA
    csm
    co
    #
    wceq
    #
    cA
    c0v
    wne
    #
    wa
    #
    wa
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
    @2
    @8
    @10
    @3
    @8
    @2
    @10
    @8
    @2
    @1
    @0
    cA
    csp
    co
    #
    wceq
    #
    @10
    @6
    @2
    @13
    wb
    @7
    @6
    @2
    cA
    @5
    csp
    co
    #
    cr
    wcel
    #
    @13
    @6
    @1
    @14
    cr
    @0
    @5
    cA
    csp
    oveq2
    #
    eleq1d
    @6
    @13
    @14
    @5
    cA
    csp
    co
    #
    wceq
    #
    @15
    @6
    @1
    @14
    @12
    @17
    @16
    @0
    @5
    cA
    csp
    oveq1
    eqeq12d
    cA
    chil
    wcel
    #
    @5
    chil
    wcel
    @15
    @18
    wb
    eigpos.1
    cB
    cA
    eigpos.2
    eigpos.1
    hvmulcli
    cA
    @5
    hire
    mp2an
    syl6rbbr
    bitrd
    adantr
    cA
    cB
    cT
    eigpos.1
    eigpos.2
    eigrei
    bitrd
    biimpac
    adantlr
    #
    @9
    @10
    cc0
    cA
    cA
    csp
    co
    #
    clt
    wbr
    #
    cc0
    cB
    @21
    cmul
    co
    #
    cle
    wbr
    #
    @11
    @20
    @7
    @22
    @4
    @6
    @19
    @7
    @22
    eigpos.1
    cA
    ax-his4
    mpan
    ad2antll
    @9
    cc0
    @1
    @23
    cle
    @2
    @3
    @8
    simplr
    @9
    @1
    @14
    @23
    @6
    @1
    @14
    wceq
    @4
    @7
    @16
    ad2antrl
    @9
    @14
    cB
    ccj
    cfv
    #
    @21
    cmul
    co
    #
    @23
    cB
    cc
    wcel
    @19
    @19
    @14
    @26
    wceq
    eigpos.2
    eigpos.1
    eigpos.1
    cB
    cA
    cA
    his5
    mp3an
    @9
    @25
    cB
    @21
    cmul
    @9
    cB
    @20
    cjred
    oveq1d
    syl5eq
    eqtrd
    breqtrd
    @10
    @21
    cr
    wcel
    #
    @22
    @24
    wa
    @11
    @19
    @27
    eigpos.1
    cA
    hiidrcl
    ax-mp
    cB
    @21
    prodge02
    mpanl2
    syl12anc
    jca
end
