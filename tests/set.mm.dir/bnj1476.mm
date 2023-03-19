include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "wal.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "eq0f.mm"
include "sylib.mm"
include "wa.mm"
include "rabeq2i.mm"
include "notbii.mm"
include "iman.mm"
include "sylbb2.mm"
include "sylg.mm"
include "bnj1142.mm"

theorem bnj1476
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cD: class D
  assume bnj1476.1: |- D = { x e. A | -. ph }
  assume bnj1476.2: |- ( ps -> D = (/) )


  assert |- ( ps -> A. x e. A ph )

  proof
    wps
    wph
    vx
    cA
    wps
    vx
    cv
    #
    cD
    wcel
    #
    wn
    #
    @0
    cA
    wcel
    #
    wph
    wi
    #
    vx
    wps
    cD
    c0
    wceq
    @2
    vx
    wal
    bnj1476.2
    vx
    cD
    vx
    cD
    wph
    wn
    #
    vx
    cA
    crab
    bnj1476.1
    @5
    vx
    cA
    nfrab1
    nfcxfr
    eq0f
    sylib
    @2
    @3
    @5
    wa
    #
    wn
    @4
    @1
    @6
    @5
    vx
    cD
    cA
    bnj1476.1
    rabeq2i
    notbii
    @3
    wph
    iman
    sylbb2
    sylg
    bnj1142
end
