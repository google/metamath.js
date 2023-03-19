include "cfcls.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "w3a.mm"
include "cnt.mm"
include "cin.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ctop.mm"
include "cuni.mm"
include "simp1.mm"
include "fclstop.mm"
include "syl.mm"
include "simp2.mm"
include "eqid.mm"
include "neii1.mm"
include "syl2anc.mm"
include "ntrss2.mm"
include "ssrin.mm"
include "ntropn.mm"
include "wb.mm"
include "fclselbas.mm"
include "snssd.mm"
include "neiint.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "snssg.mm"
include "mpbird.mm"
include "simp3.mm"
include "fclsopni.mm"
include "syl13anc.mm"
include "ssn0.mm"

theorem fclsneii
  let cA: class A
  let cS: class S
  let cF: class F
  let cJ: class J
  let cN: class N


  assert |- ( ( A e. ( J fClus F ) /\ N e. ( ( nei ` J ) ` { A } ) /\ S e. F ) -> ( N i^i S ) =/= (/) )

  proof
    cA
    cJ
    cF
    cfcls
    co
    wcel
    #
    cN
    cA
    csn
    #
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    cS
    cF
    wcel
    #
    w3a
    #
    cN
    cJ
    cnt
    cfv
    cfv
    #
    cS
    cin
    #
    cN
    cS
    cin
    #
    wss
    #
    @6
    c0
    wne
    #
    @7
    c0
    wne
    @4
    @5
    cN
    wss
    #
    @8
    @4
    cJ
    ctop
    wcel
    #
    cN
    cJ
    cuni
    #
    wss
    #
    @10
    @4
    @0
    @11
    @0
    @2
    @3
    simp1
    #
    cA
    cF
    cJ
    fclstop
    syl
    #
    @4
    @11
    @2
    @13
    @15
    @0
    @2
    @3
    simp2
    #
    @1
    cJ
    cN
    @12
    @12
    eqid
    #
    neii1
    syl2anc
    #
    cN
    cJ
    @12
    @17
    ntrss2
    syl2anc
    @5
    cN
    cS
    ssrin
    syl
    @4
    @0
    @5
    cJ
    wcel
    #
    cA
    @5
    wcel
    #
    @3
    @9
    @14
    @4
    @11
    @13
    @19
    @15
    @18
    cN
    cJ
    @12
    @17
    ntropn
    syl2anc
    @4
    @20
    @1
    @5
    wss
    #
    @4
    @2
    @21
    @16
    @4
    @11
    @1
    @12
    wss
    @13
    @2
    @21
    wb
    @15
    @4
    cA
    @12
    @4
    @0
    cA
    @12
    wcel
    #
    @14
    cA
    cF
    cJ
    @12
    @17
    fclselbas
    syl
    #
    snssd
    @18
    @1
    cJ
    cN
    @12
    @17
    neiint
    syl3anc
    mpbid
    @4
    @22
    @20
    @21
    wb
    @23
    cA
    @5
    @12
    snssg
    syl
    mpbird
    @0
    @2
    @3
    simp3
    cA
    cS
    @5
    cF
    cJ
    fclsopni
    syl13anc
    @6
    @7
    ssn0
    syl2anc
end
