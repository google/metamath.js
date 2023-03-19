include "wss.mm"
include "wcel.mm"
include "cpw.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "catm.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "wa.mm"
include "cmpt.mm"
include "pclfvalN.mm"
include "fveq1d.mm"
include "adantr.mm"
include "simpr.mm"
include "c0.mm"
include "wne.mm"
include "elpwi.mm"
include "adantl.mm"
include "wb.mm"
include "atpsubN.mm"
include "sseq2.mm"
include "elrab3.mm"
include "syl.mm"
include "mpbird.mm"
include "ne0i.mm"
include "intex.mm"
include "sylib.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "sylan2br.mm"

theorem pclvalN
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume pclfval.a: |- A = ( Atoms ` K )
  assume pclfval.s: |- S = ( PSubSp ` K )
  assume pclfval.c: |- U = ( PCl ` K )

  disjoint A y
  disjoint K y
  disjoint S y
  disjoint X y
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint K k
  disjoint K x
  disjoint S k
  disjoint S x
  disjoint X x
  assert |- ( ( K e. V /\ X C_ A ) -> ( U ` X ) = |^| { y e. S | X C_ y } )

  proof
    cX
    cA
    wss
    #
    cK
    cV
    wcel
    #
    cX
    cA
    cpw
    #
    wcel
    #
    cX
    cU
    cfv
    #
    cX
    vy
    cv
    #
    wss
    #
    vy
    cS
    crab
    #
    cint
    #
    wceq
    cX
    cA
    cA
    cK
    catm
    cfv
    cvv
    pclfval.a
    cK
    catm
    fvex
    eqeltri
    elpw2
    @1
    @3
    wa
    #
    @4
    cX
    vx
    @2
    vx
    cv
    #
    @5
    wss
    #
    vy
    cS
    crab
    #
    cint
    #
    cmpt
    #
    cfv
    #
    @8
    @1
    @4
    @15
    wceq
    @3
    @1
    cX
    cU
    @14
    vx
    vy
    cA
    cS
    cU
    cK
    cV
    pclfval.a
    pclfval.s
    pclfval.c
    pclfvalN
    fveq1d
    adantr
    @9
    @3
    @8
    cvv
    wcel
    #
    @15
    @8
    wceq
    @1
    @3
    simpr
    @9
    @7
    c0
    wne
    #
    @16
    @9
    cA
    @7
    wcel
    #
    @17
    @9
    @18
    @0
    @3
    @0
    @1
    cX
    cA
    elpwi
    adantl
    @9
    cA
    cS
    wcel
    #
    @18
    @0
    wb
    @1
    @19
    @3
    cA
    cS
    cK
    cV
    pclfval.a
    pclfval.s
    atpsubN
    adantr
    @6
    @0
    vy
    cA
    cS
    @5
    cA
    cX
    sseq2
    elrab3
    syl
    mpbird
    @7
    cA
    ne0i
    syl
    @7
    intex
    sylib
    vx
    cX
    @13
    @8
    @2
    cvv
    @14
    @10
    cX
    wceq
    #
    @12
    @7
    @20
    @11
    @6
    vy
    cS
    @10
    cX
    @5
    sseq1
    rabbidv
    inteqd
    @14
    eqid
    fvmptg
    syl2anc
    eqtrd
    sylan2br
end
