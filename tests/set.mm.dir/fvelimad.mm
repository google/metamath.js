include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cin.mm"
include "wrex.mm"
include "wbr.mm"
include "cima.mm"
include "wcel.mm"
include "elimag.mm"
include "ibi.mm"
include "syl.mm"
include "nfv.mm"
include "nfre1.mm"
include "w3a.mm"
include "wa.mm"
include "cdm.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "adantr.mm"
include "simpr.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "fndmd.mm"
include "eleqtrd.mm"
include "3adant2.mm"
include "simp2.mm"
include "elind.mm"
include "wfun.mm"
include "wfn.mm"
include "fnfun.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "funbrfv.mm"
include "sylc.mm"
include "rspe.mm"
include "syl2anc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvrex.mm"
include "sylibr.mm"

theorem fvelimad
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  assume fvelimad.x: |- F/_ x F
  assume fvelimad.f: |- ( ph -> F Fn A )
  assume fvelimad.c: |- ( ph -> C e. ( F " B ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint F y
  disjoint ph y
  assert |- ( ph -> E. x e. ( A i^i B ) ( F ` x ) = C )

  proof
    wph
    vy
    cv
    #
    cF
    cfv
    #
    cC
    wceq
    #
    vy
    cA
    cB
    cin
    #
    wrex
    #
    vx
    cv
    #
    cF
    cfv
    #
    cC
    wceq
    #
    vx
    @3
    wrex
    wph
    @0
    cC
    cF
    wbr
    #
    vy
    cB
    wrex
    #
    @4
    wph
    cC
    cF
    cB
    cima
    #
    wcel
    #
    @9
    fvelimad.c
    @11
    @9
    vy
    cC
    cF
    cB
    @10
    elimag
    ibi
    syl
    wph
    @8
    @4
    vy
    cB
    wph
    vy
    nfv
    @2
    vy
    @3
    nfre1
    wph
    @0
    cB
    wcel
    #
    @8
    @4
    wph
    @12
    @8
    w3a
    #
    @0
    @3
    wcel
    @2
    @4
    @13
    cA
    cB
    @0
    wph
    @8
    @0
    cA
    wcel
    @12
    wph
    @8
    wa
    #
    @0
    cF
    cdm
    #
    cA
    @14
    @0
    cvv
    wcel
    #
    @11
    @8
    @0
    @15
    wcel
    @16
    @14
    vy
    vex
    a1i
    wph
    @11
    @8
    fvelimad.c
    adantr
    wph
    @8
    simpr
    @0
    cC
    cvv
    @10
    cF
    breldmg
    syl3anc
    wph
    @15
    cA
    wceq
    @8
    wph
    cA
    cF
    fvelimad.f
    fndmd
    adantr
    eleqtrd
    3adant2
    wph
    @12
    @8
    simp2
    elind
    @13
    cF
    wfun
    #
    @8
    @2
    wph
    @12
    @17
    @8
    wph
    cF
    cA
    wfn
    @17
    fvelimad.f
    cA
    cF
    fnfun
    syl
    3ad2ant1
    wph
    @12
    @8
    simp3
    @0
    cC
    cF
    funbrfv
    sylc
    @2
    vy
    @3
    rspe
    syl2anc
    3exp
    rexlimd
    mpd
    @7
    @2
    vx
    vy
    @3
    @7
    vy
    nfv
    vx
    @1
    cC
    vx
    @0
    cF
    fvelimad.x
    vx
    @0
    nfcv
    nffv
    vx
    cC
    nfcv
    nfeq
    @5
    @0
    wceq
    @6
    @1
    cC
    @5
    @0
    cF
    fveq2
    eqeq1d
    cbvrex
    sylibr
end
