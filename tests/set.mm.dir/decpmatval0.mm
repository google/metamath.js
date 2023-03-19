include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cdecpmat.mm"
include "wceq.mm"
include "df-decpmat.mm"
include "a1i.mm"
include "dmeq.mm"
include "adantr.mm"
include "dmeqd.mm"
include "oveq.mm"
include "fveq2d.mm"
include "simpr.mm"
include "fveq12d.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "elex.mm"
include "dmexg.mm"
include "syl.mm"
include "jca.mm"
include "mpt2exga.mm"
include "ovmpt2d.mm"

theorem decpmatval0
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cV: class V
  let vk: setvar k
  let vm: setvar m

  disjoint K i
  disjoint K j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint K k
  disjoint K m
  disjoint i k
  disjoint i m
  disjoint j k
  disjoint j m
  disjoint k m
  disjoint M k
  disjoint M m
  disjoint V k
  disjoint V m
  assert |- ( ( M e. V /\ K e. NN0 ) -> ( M decompPMat K ) = ( i e. dom dom M , j e. dom dom M |-> ( ( coe1 ` ( i M j ) ) ` K ) ) )

  proof
    cM
    cV
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    #
    vm
    vk
    cM
    cK
    cvv
    cn0
    vi
    vj
    vm
    cv
    #
    cdm
    #
    cdm
    #
    @5
    vk
    cv
    #
    vi
    cv
    #
    vj
    cv
    #
    @3
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    vi
    vj
    cM
    cdm
    #
    cdm
    #
    @14
    cK
    @7
    @8
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    cdecpmat
    cvv
    cdecpmat
    vm
    vk
    cvv
    cn0
    @12
    cmpt2
    wceq
    @2
    vi
    vj
    vk
    vm
    df-decpmat
    a1i
    @3
    cM
    wceq
    #
    @6
    cK
    wceq
    #
    wa
    #
    @12
    @18
    wceq
    @2
    @21
    vi
    vj
    @5
    @5
    @11
    @14
    @14
    @17
    @21
    @4
    @13
    @19
    @4
    @13
    wceq
    @20
    @3
    cM
    dmeq
    adantr
    dmeqd
    #
    @22
    @21
    @6
    cK
    @10
    @16
    @19
    @10
    @16
    wceq
    @20
    @19
    @9
    @15
    cco1
    @7
    @8
    @3
    cM
    oveq
    fveq2d
    adantr
    @19
    @20
    simpr
    fveq12d
    mpt2eq123dv
    adantl
    @0
    cM
    cvv
    wcel
    @1
    cM
    cV
    elex
    adantr
    @0
    @1
    simpr
    @2
    @14
    cvv
    wcel
    #
    @23
    wa
    #
    @18
    cvv
    wcel
    @0
    @24
    @1
    @0
    @23
    @23
    @0
    @13
    cvv
    wcel
    @23
    cM
    cV
    dmexg
    @13
    cvv
    dmexg
    syl
    #
    @25
    jca
    adantr
    vi
    vj
    @14
    @14
    @17
    cvv
    cvv
    mpt2exga
    syl
    ovmpt2d
end
