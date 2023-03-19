include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cint.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "wceq.mm"
include "wa.mm"
include "cfil.mm"
include "wss.mm"
include "simpl.mm"
include "csn.mm"
include "cfg.mm"
include "co.mm"
include "cfbas.mm"
include "ufilfil.mm"
include "filtop.mm"
include "syl.mm"
include "adantr.mm"
include "cuni.mm"
include "c0.mm"
include "wne.mm"
include "filn0.mm"
include "intssuni.mm"
include "3syl.mm"
include "filunibas.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "uffix.mm"
include "syl2anc.mm"
include "simprd.mm"
include "simpld.mm"
include "fgcl.mm"
include "eqeltrd.mm"
include "wral.mm"
include "filsspw.mm"
include "elintg.mm"
include "ibi.mm"
include "adantl.mm"
include "ssrab.mm"
include "sylanbrc.mm"
include "ufilmax.mm"
include "syl3anc.mm"
include "eqimss.mm"
include "simprbi.mm"
include "wb.mm"
include "eleq2.mm"
include "biimpac.mm"
include "sylan.mm"
include "elrab.mm"
include "mpbird.mm"
include "impbida.mm"

theorem uffixfr
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint X x
  disjoint x y
  disjoint F y
  disjoint X y
  assert |- ( F e. ( UFil ` X ) -> ( A e. |^| F <-> F = { x e. ~P X | A e. x } ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cA
    cF
    cint
    #
    wcel
    #
    cF
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cX
    cpw
    #
    crab
    #
    wceq
    #
    @0
    @2
    wa
    #
    @0
    @6
    cX
    cfil
    cfv
    #
    wcel
    cF
    @6
    wss
    #
    @7
    @0
    @2
    simpl
    @8
    @6
    cX
    cA
    csn
    csn
    #
    cfg
    co
    #
    @9
    @8
    @11
    cX
    cfbas
    cfv
    wcel
    #
    @6
    @12
    wceq
    #
    @8
    cX
    cF
    wcel
    #
    cA
    cX
    wcel
    #
    @13
    @14
    wa
    @0
    @15
    @2
    @0
    cF
    @9
    wcel
    #
    @15
    cF
    cX
    ufilfil
    #
    cF
    cX
    filtop
    syl
    #
    adantr
    @0
    @1
    cX
    cA
    @0
    @1
    cF
    cuni
    #
    cX
    @0
    @17
    cF
    c0
    wne
    @1
    @20
    wss
    @18
    cF
    cX
    filn0
    cF
    intssuni
    3syl
    @0
    @17
    @20
    cX
    wceq
    @18
    cF
    cX
    filunibas
    syl
    sseqtrd
    sselda
    vx
    cA
    cF
    cX
    uffix
    syl2anc
    #
    simprd
    @8
    @13
    @12
    @9
    wcel
    @8
    @13
    @14
    @21
    simpld
    @11
    cX
    fgcl
    syl
    eqeltrd
    @8
    cF
    @5
    wss
    #
    @4
    vx
    cF
    wral
    #
    @10
    @8
    @17
    @22
    @0
    @17
    @2
    @18
    adantr
    cF
    cX
    filsspw
    syl
    @2
    @23
    @0
    @2
    @23
    vx
    cA
    cF
    @1
    elintg
    ibi
    adantl
    @4
    vx
    @5
    cF
    ssrab
    #
    sylanbrc
    cF
    @6
    cX
    ufilmax
    syl3anc
    @0
    @7
    wa
    #
    @2
    @23
    @25
    @10
    @23
    @7
    @10
    @0
    cF
    @6
    eqimss
    adantl
    @10
    @22
    @23
    @24
    simprbi
    syl
    @25
    cX
    @6
    wcel
    #
    @16
    @2
    @23
    wb
    @0
    @15
    @7
    @26
    @19
    @7
    @15
    @26
    cF
    @6
    cX
    eleq2
    biimpac
    sylan
    @26
    cX
    @5
    wcel
    @16
    @4
    @16
    vx
    cX
    @5
    @3
    cX
    cA
    eleq2
    elrab
    simprbi
    vx
    cA
    cF
    cX
    elintg
    3syl
    mpbird
    impbida
end
