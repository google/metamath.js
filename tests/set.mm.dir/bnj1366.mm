include "cio.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "weu.mm"
include "wral.mm"
include "wceq.mm"
include "simp3bi.mm"
include "cv.mm"
include "wb.mm"
include "wal.mm"
include "simp2bi.mm"
include "nfcv.mm"
include "nfeu1.mm"
include "nfral.mm"
include "nfra1.mm"
include "wa.mm"
include "rspa.mm"
include "iota1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "syl.mm"
include "rexbida.mm"
include "abid.mm"
include "eqid.mm"
include "iotaex.mm"
include "elrnmpti.mm"
include "3bitr4g.mm"
include "alrimi.mm"
include "nfab1.mm"
include "nfiota1.mm"
include "nfmpt.mm"
include "nfrn.mm"
include "cleqf.mm"
include "sylibr.mm"
include "eqtrd.mm"
include "simp1bi.mm"
include "mptexg.mm"
include "rnexg.mm"
include "3syl.mm"
include "eqeltrd.mm"

theorem bnj1366
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume bnj1366.1: |- ( ps <-> ( A e. _V /\ A. x e. A E! y ph /\ B = { y | E. x e. A ph } ) )

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ps -> B e. _V )

  proof
    wps
    cB
    vx
    cA
    wph
    vy
    cio
    #
    cmpt
    #
    crn
    #
    cvv
    wps
    cB
    wph
    vx
    cA
    wrex
    #
    vy
    cab
    #
    @2
    wps
    cA
    cvv
    wcel
    #
    wph
    vy
    weu
    #
    vx
    cA
    wral
    #
    cB
    @4
    wceq
    #
    bnj1366.1
    simp3bi
    wps
    vy
    cv
    #
    @4
    wcel
    #
    @9
    @2
    wcel
    #
    wb
    #
    vy
    wal
    #
    @4
    @2
    wceq
    wps
    @7
    @13
    wps
    @5
    @7
    @8
    bnj1366.1
    simp2bi
    @7
    @12
    vy
    @6
    vy
    vx
    cA
    vy
    cA
    nfcv
    #
    wph
    vy
    nfeu1
    nfral
    @7
    @3
    @9
    @0
    wceq
    #
    vx
    cA
    wrex
    @10
    @11
    @7
    wph
    @15
    vx
    cA
    @6
    vx
    cA
    nfra1
    @7
    vx
    cv
    cA
    wcel
    wa
    @6
    wph
    @15
    wb
    @6
    vx
    cA
    rspa
    @6
    wph
    @0
    @9
    wceq
    @15
    wph
    vy
    iota1
    @0
    @9
    eqcom
    syl6bb
    syl
    rexbida
    @3
    vy
    abid
    vx
    cA
    @0
    @9
    @1
    @1
    eqid
    wph
    vy
    iotaex
    elrnmpti
    3bitr4g
    alrimi
    syl
    vy
    @4
    @2
    @3
    vy
    nfab1
    vy
    @1
    vy
    vx
    cA
    @0
    @14
    wph
    vy
    nfiota1
    nfmpt
    nfrn
    cleqf
    sylibr
    eqtrd
    wps
    @5
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    wps
    @5
    @7
    @8
    bnj1366.1
    simp1bi
    vx
    cA
    @0
    cvv
    mptexg
    @1
    cvv
    rnexg
    3syl
    eqeltrd
end
