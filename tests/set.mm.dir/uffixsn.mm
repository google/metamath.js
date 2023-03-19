include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cint.mm"
include "wa.mm"
include "csn.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "cuni.mm"
include "cfil.mm"
include "c0.mm"
include "wne.mm"
include "ufilfil.mm"
include "filn0.mm"
include "intssuni.mm"
include "3syl.mm"
include "wceq.mm"
include "filunibas.mm"
include "syl.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "snssd.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "snidg.mm"
include "adantl.mm"
include "eleq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "uffixfr.mm"
include "biimpa.mm"
include "eleqtrrd.mm"

theorem uffixsn
  let cA: class A
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( UFil ` X ) /\ A e. |^| F ) -> { A } e. F )

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
    wa
    #
    cA
    csn
    #
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
    cF
    @3
    @4
    @7
    wcel
    #
    cA
    @4
    wcel
    #
    @4
    @8
    wcel
    @3
    @4
    cX
    wss
    @9
    @3
    cA
    cX
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
    cF
    cX
    cfil
    cfv
    wcel
    #
    cF
    c0
    wne
    @1
    @11
    wss
    cF
    cX
    ufilfil
    #
    cF
    cX
    filn0
    cF
    intssuni
    3syl
    @0
    @12
    @11
    cX
    wceq
    @13
    cF
    cX
    filunibas
    syl
    sseqtrd
    sselda
    snssd
    @4
    cX
    cA
    snex
    elpw
    sylibr
    @2
    @10
    @0
    cA
    @1
    snidg
    adantl
    @6
    @10
    vx
    @4
    @7
    @5
    @4
    cA
    eleq2
    elrab
    sylanbrc
    @0
    @2
    cF
    @8
    wceq
    vx
    cA
    cF
    cX
    uffixfr
    biimpa
    eleqtrrd
end
