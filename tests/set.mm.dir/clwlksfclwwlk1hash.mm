include "cv.mm"
include "wcel.mm"
include "cclwlks.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "rabeq2i.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cvtx.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "clwlkcompim.mm"
include "cn0.mm"
include "wfn.mm"
include "lencl.mm"
include "ffn.mm"
include "fnfz0hash.mm"
include "wi.mm"
include "nn0fz0.mm"
include "fzelp1.mm"
include "sylbi.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "mpd.mm"
include "syl2an.mm"
include "syl.mm"

theorem clwlksfclwwlk1hash
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let cW: class W
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint W c
  assert |- ( c e. C -> ( # ` A ) e. ( 0 ... ( # ` B ) ) )

  proof
    vc
    cv
    #
    cC
    wcel
    @0
    cG
    cclwlks
    cfv
    #
    wcel
    #
    cA
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    @3
    cc0
    cB
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @4
    vc
    cC
    @1
    clwlksfclwwlk.c
    rabeq2i
    @2
    @7
    @4
    @2
    cA
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    #
    cc0
    @3
    cfz
    co
    #
    cG
    cvtx
    cfv
    #
    cB
    wf
    #
    wa
    #
    vi
    cv
    #
    cB
    cfv
    #
    @15
    c1
    caddc
    co
    cB
    cfv
    #
    wceq
    @15
    cA
    cfv
    @8
    cfv
    #
    @16
    csn
    wceq
    @16
    @17
    cpr
    @18
    wss
    wif
    vi
    cc0
    @3
    cfzo
    co
    wral
    cc0
    cB
    cfv
    @3
    cB
    cfv
    wceq
    wa
    #
    wa
    @7
    cB
    vi
    cA
    cG
    @8
    @12
    @0
    @12
    eqid
    @8
    eqid
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlkcompim
    @14
    @7
    @19
    @10
    @3
    cn0
    wcel
    #
    cB
    @11
    wfn
    #
    @7
    @13
    @9
    cA
    lencl
    @11
    @12
    cB
    ffn
    @20
    @21
    wa
    @5
    @3
    c1
    caddc
    co
    #
    wceq
    #
    @7
    cB
    @3
    fnfz0hash
    @20
    @23
    @7
    wi
    @21
    @20
    @7
    @23
    @3
    cc0
    @22
    cfz
    co
    #
    wcel
    #
    @20
    @3
    @11
    wcel
    @25
    @3
    nn0fz0
    @3
    cc0
    @3
    fzelp1
    sylbi
    @23
    @6
    @24
    @3
    @5
    @22
    cc0
    cfz
    oveq2
    eleq2d
    syl5ibrcom
    adantr
    mpd
    syl2an
    adantr
    syl
    adantr
    sylbi
end
