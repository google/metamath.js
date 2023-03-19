include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "cee.mm"
include "cfv.mm"
include "cr.mm"
include "wf.mm"
include "wral.mm"
include "elee.mm"
include "crn.mm"
include "wss.mm"
include "wfn.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "df-f.mm"
include "mpbiran.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "sseq1i.mm"
include "wi.mm"
include "wal.mm"
include "abss.mm"
include "nfre1.mm"
include "nfv.mm"
include "nfim.mm"
include "nfal.mm"
include "r19.23v.mm"
include "albii.mm"
include "ralcom4.mm"
include "rsp.mm"
include "clel2.mm"
include "syl6ibr.mm"
include "sylbir.mm"
include "ralrimi.mm"
include "nfra1.mm"
include "eleq1a.mm"
include "syl6.mm"
include "rexlimd.mm"
include "alrimiv.mm"
include "impbii.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem mptelee
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cN: class N
  let va: setvar a

  disjoint N k
  disjoint N a
  disjoint a k
  disjoint A a
  disjoint B a
  disjoint F a
  assert |- ( N e. NN -> ( ( k e. ( 1 ... N ) |-> ( A F B ) ) e. ( EE ` N ) <-> A. k e. ( 1 ... N ) ( A F B ) e. RR ) )

  proof
    cN
    cn
    wcel
    vk
    c1
    cN
    cfz
    co
    #
    cA
    cB
    cF
    co
    #
    cmpt
    #
    cN
    cee
    cfv
    wcel
    @0
    cr
    @2
    wf
    #
    @1
    cr
    wcel
    #
    vk
    @0
    wral
    #
    @2
    cN
    elee
    @3
    @2
    crn
    #
    cr
    wss
    #
    @5
    @3
    @2
    @0
    wfn
    @7
    vk
    @0
    @1
    @2
    cA
    cB
    cF
    ovex
    #
    @2
    eqid
    #
    fnmpti
    @0
    cr
    @2
    df-f
    mpbiran
    @7
    va
    cv
    #
    @1
    wceq
    #
    vk
    @0
    wrex
    #
    va
    cab
    #
    cr
    wss
    #
    @5
    @6
    @13
    cr
    vk
    va
    @0
    @1
    @2
    @9
    rnmpt
    sseq1i
    @14
    @12
    @10
    cr
    wcel
    #
    wi
    #
    va
    wal
    #
    @5
    @12
    va
    cr
    abss
    @17
    @5
    @17
    @4
    vk
    @0
    @16
    vk
    va
    @12
    @15
    vk
    @11
    vk
    @0
    nfre1
    @15
    vk
    nfv
    #
    nfim
    nfal
    @17
    @11
    @15
    wi
    #
    vk
    @0
    wral
    #
    va
    wal
    #
    vk
    cv
    @0
    wcel
    #
    @4
    wi
    #
    @20
    @16
    va
    @11
    @15
    vk
    @0
    r19.23v
    albii
    @21
    @19
    va
    wal
    #
    vk
    @0
    wral
    #
    @23
    @19
    vk
    va
    @0
    ralcom4
    @25
    @22
    @24
    @4
    @24
    vk
    @0
    rsp
    va
    @1
    cr
    @8
    clel2
    syl6ibr
    sylbir
    sylbir
    ralrimi
    @5
    @16
    va
    @5
    @11
    @15
    vk
    @0
    @4
    vk
    @0
    nfra1
    @18
    @5
    @22
    @4
    @19
    @4
    vk
    @0
    rsp
    @1
    cr
    @10
    eleq1a
    syl6
    rexlimd
    alrimiv
    impbii
    bitri
    bitri
    bitri
    syl6bb
end
