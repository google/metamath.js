include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "caddc.mm"
include "cmul.mm"
include "cpc.mm"
include "eqid.mm"
include "pcpremul.mm"
include "wceq.mm"
include "pczpre.mm"
include "3adant3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "zmulcl.mm"
include "ad2ant2r.mm"
include "cc.mm"
include "zcn.mm"
include "anim1i.mm"
include "mulne0.mm"
include "syl2an.mm"
include "jca.mm"
include "sylan2.mm"
include "3impb.mm"
include "3eqtr4rd.mm"

theorem pcmul
  let cA: class A
  let cB: class B
  let cP: class P
  let vn: setvar n


  assert |- ( ( P e. Prime /\ ( A e. ZZ /\ A =/= 0 ) /\ ( B e. ZZ /\ B =/= 0 ) ) -> ( P pCnt ( A x. B ) ) = ( ( P pCnt A ) + ( P pCnt B ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cz
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cP
    vn
    cv
    cexp
    co
    #
    cA
    cdvds
    wbr
    vn
    cn0
    crab
    cr
    clt
    csup
    #
    @8
    cB
    cdvds
    wbr
    vn
    cn0
    crab
    cr
    clt
    csup
    #
    caddc
    co
    @8
    cA
    cB
    cmul
    co
    #
    cdvds
    wbr
    vn
    cn0
    crab
    cr
    clt
    csup
    #
    cP
    cA
    cpc
    co
    #
    cP
    cB
    cpc
    co
    #
    caddc
    co
    cP
    @11
    cpc
    co
    #
    cP
    @9
    @10
    @12
    vn
    cA
    cB
    @9
    eqid
    #
    @10
    eqid
    #
    @12
    eqid
    #
    pcpremul
    @7
    @13
    @9
    @14
    @10
    caddc
    @0
    @3
    @13
    @9
    wceq
    @6
    cP
    @9
    vn
    cA
    @16
    pczpre
    3adant3
    @0
    @6
    @14
    @10
    wceq
    @3
    cP
    @10
    vn
    cB
    @17
    pczpre
    3adant2
    oveq12d
    @0
    @3
    @6
    @15
    @12
    wceq
    #
    @3
    @6
    wa
    #
    @0
    @11
    cz
    wcel
    #
    @11
    cc0
    wne
    #
    wa
    @19
    @20
    @21
    @22
    @1
    @4
    @21
    @2
    @5
    cA
    cB
    zmulcl
    ad2ant2r
    @3
    cA
    cc
    wcel
    #
    @2
    wa
    cB
    cc
    wcel
    #
    @5
    wa
    @22
    @6
    @1
    @23
    @2
    cA
    zcn
    anim1i
    @4
    @24
    @5
    cB
    zcn
    anim1i
    cA
    cB
    mulne0
    syl2an
    jca
    cP
    @12
    vn
    @11
    @18
    pczpre
    sylan2
    3impb
    3eqtr4rd
end
