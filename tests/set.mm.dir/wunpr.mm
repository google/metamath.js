include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wral.mm"
include "cwun.mm"
include "cuni.mm"
include "cpw.mm"
include "w3a.mm"
include "wtr.mm"
include "c0.mm"
include "wne.mm"
include "iswun.mm"
include "ibi.mm"
include "simp3d.mm"
include "simp3.mm"
include "ralimi.mm"
include "3syl.mm"
include "wceq.mm"
include "preq1.mm"
include "eleq1d.mm"
include "preq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"

theorem wunpr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )
  assume wunpr.3: |- ( ph -> B e. U )


  assert |- ( ph -> { A , B } e. U )

  proof
    wph
    cA
    cU
    wcel
    cB
    cU
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cU
    wcel
    #
    vy
    cU
    wral
    #
    vx
    cU
    wral
    #
    cA
    cB
    cpr
    #
    cU
    wcel
    #
    wununi.2
    wunpr.3
    wph
    cU
    cwun
    wcel
    #
    @0
    cuni
    cU
    wcel
    #
    @0
    cpw
    cU
    wcel
    #
    @4
    w3a
    #
    vx
    cU
    wral
    #
    @5
    wununi.1
    @8
    cU
    wtr
    #
    cU
    c0
    wne
    #
    @12
    @8
    @13
    @14
    @12
    w3a
    vx
    vy
    cU
    cwun
    iswun
    ibi
    simp3d
    @11
    @4
    vx
    cU
    @9
    @10
    @4
    simp3
    ralimi
    3syl
    @3
    @7
    cA
    @1
    cpr
    #
    cU
    wcel
    vx
    vy
    cA
    cB
    cU
    cU
    @0
    cA
    wceq
    @2
    @15
    cU
    @0
    cA
    @1
    preq1
    eleq1d
    @1
    cB
    wceq
    @15
    @6
    cU
    @1
    cB
    cA
    preq2
    eleq1d
    rspc2va
    syl21anc
end
