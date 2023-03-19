include "cv.mm"
include "wcel.mm"
include "cclwlks.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cvtx.mm"
include "cword.mm"
include "rabeq2i.mm"
include "ciedg.mm"
include "cdm.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
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
include "lencl.mm"
include "cz.mm"
include "nn0z.mm"
include "fzval3.mm"
include "syl.mm"
include "feq2d.mm"
include "biimpa.mm"
include "iswrdi.mm"
include "sylan.mm"
include "adantr.mm"
include "sylbi.mm"

theorem clwlksfclwwlk2wrd
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  assert |- ( c e. C -> B e. Word ( Vtx ` G ) )

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
    cB
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @4
    vc
    cC
    @1
    clwlksfclwwlk.c
    rabeq2i
    @2
    @6
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
    @5
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
    @13
    c1
    caddc
    co
    cB
    cfv
    #
    wceq
    @13
    cA
    cfv
    @7
    cfv
    #
    @14
    csn
    wceq
    @14
    @15
    cpr
    @16
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
    @6
    cB
    vi
    cA
    cG
    @7
    @5
    @0
    @5
    eqid
    @7
    eqid
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlkcompim
    @12
    @6
    @17
    @9
    @3
    cn0
    wcel
    #
    @11
    @6
    @8
    cA
    lencl
    @18
    @11
    wa
    cc0
    @3
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @5
    cB
    wf
    #
    @6
    @18
    @11
    @21
    @18
    @10
    @20
    @5
    cB
    @18
    @3
    cz
    wcel
    @10
    @20
    wceq
    @3
    nn0z
    cc0
    @3
    fzval3
    syl
    feq2d
    biimpa
    @5
    @19
    cB
    iswrdi
    syl
    sylan
    adantr
    syl
    adantr
    sylbi
end
