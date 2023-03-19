include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cxrs.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cesum.mm"
include "xrge0base.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "ctps.mm"
include "xrge0tps.mm"
include "simpl.mm"
include "nfel1.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfcv.mm"
include "simpr.mm"
include "r19.21bi.mm"
include "eqid.mm"
include "fmptdF.mm"
include "tsmscl.mm"
include "cuni.mm"
include "wceq.mm"
include "df-esum.mm"
include "xrge0tsmsbi.mm"
include "mpbiri.mm"
include "sseldd.mm"

theorem esumcl
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  assume esumcl.1: |- F/_ k A

  disjoint V k
  assert |- ( ( A e. V /\ A. k e. A B e. ( 0 [,] +oo ) ) -> sum* k e. A B e. ( 0 [,] +oo ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    vk
    cA
    wral
    #
    wa
    #
    cxrs
    @1
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    ctsu
    co
    #
    @1
    cA
    cB
    vk
    cesum
    #
    @4
    cA
    @1
    @6
    @5
    cV
    xrge0base
    @5
    ccmn
    wcel
    @4
    xrge0cmn
    a1i
    @5
    ctps
    wcel
    @4
    xrge0tps
    a1i
    @0
    @3
    simpl
    #
    @4
    vk
    cA
    cB
    @1
    @6
    @0
    @3
    vk
    vk
    cA
    cV
    esumcl.1
    nfel1
    @2
    vk
    cA
    nfra1
    nfan
    esumcl.1
    vk
    @1
    nfcv
    @4
    @2
    vk
    cA
    @0
    @3
    simpr
    r19.21bi
    @6
    eqid
    fmptdF
    #
    tsmscl
    @4
    @8
    @7
    wcel
    @8
    @7
    cuni
    wceq
    cA
    cB
    vk
    df-esum
    @4
    cA
    @8
    @6
    @5
    cV
    @5
    eqid
    @9
    @10
    xrge0tsmsbi
    mpbiri
    sseldd
end
