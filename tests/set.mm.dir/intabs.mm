include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "intmin3.mm"
include "wn.mm"
include "intnex.mm"
include "ssv.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "pm2.61i.mm"
include "cbvabv.mm"
include "inteqi.mm"
include "sseqtr4i.mm"
include "simpr.mm"
include "ss2abi.mm"
include "intss.mm"
include "ax-mp.mm"
include "eqssi.mm"

theorem intabs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume intabs.1: |- ( x = y -> ( ph <-> ps ) )
  assume intabs.2: |- ( x = |^| { y | ps } -> ( ph <-> ch ) )
  assume intabs.3: |- ( |^| { y | ps } C_ A /\ ch )

  disjoint x y
  disjoint A x
  disjoint ph y
  disjoint ps x
  disjoint ch x
  assert |- |^| { x | ( x C_ A /\ ph ) } = |^| { x | ph }

  proof
    vx
    cv
    #
    cA
    wss
    #
    wph
    wa
    #
    vx
    cab
    #
    cint
    #
    wph
    vx
    cab
    #
    cint
    #
    @4
    wps
    vy
    cab
    #
    cint
    #
    @6
    @8
    cvv
    wcel
    #
    @4
    @8
    wss
    #
    @2
    @8
    cA
    wss
    #
    wch
    wa
    vx
    @8
    cvv
    @0
    @8
    wceq
    @1
    @11
    wph
    wch
    @0
    @8
    cA
    sseq1
    intabs.2
    anbi12d
    intabs.3
    intmin3
    @9
    wn
    @8
    cvv
    wceq
    #
    @10
    @7
    intnex
    @12
    @10
    @4
    cvv
    wss
    @4
    ssv
    @8
    cvv
    @4
    sseq2
    mpbiri
    sylbi
    pm2.61i
    @5
    @7
    wph
    wps
    vx
    vy
    intabs.1
    cbvabv
    inteqi
    sseqtr4i
    @3
    @5
    wss
    @6
    @4
    wss
    @2
    wph
    vx
    @1
    wph
    simpr
    ss2abi
    @3
    @5
    intss
    ax-mp
    eqssi
end
