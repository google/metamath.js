include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "csn.mm"
include "0ex.mm"
include "snnz.mm"
include "eqnetri.mm"
include "n0.mm"
include "mpbi.mm"
include "wi.mm"
include "biimt.mm"
include "iman.mm"
include "anbi2i.mm"
include "xchbinxr.mm"
include "syl6bb.mm"
include "xor3.mm"
include "sylibr.mm"
include "eximii.mm"
include "exnal.mm"
include "nex.mm"

theorem notzfaus
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume notzfaus.1: |- A = { (/) }
  assume notzfaus.2: |- ( ph <-> -. x e. y )

  disjoint A x
  assert |- -. E. y A. x ( x e. y <-> ( x e. A /\ ph ) )

  proof
    vx
    cv
    #
    vy
    cv
    wcel
    #
    @0
    cA
    wcel
    #
    wph
    wa
    #
    wb
    #
    vx
    wal
    #
    vy
    @4
    wn
    #
    vx
    wex
    @5
    wn
    @2
    @6
    vx
    cA
    c0
    wne
    @2
    vx
    wex
    cA
    c0
    csn
    c0
    notzfaus.1
    c0
    0ex
    snnz
    eqnetri
    vx
    cA
    n0
    mpbi
    @2
    @1
    @3
    wn
    #
    wb
    @6
    @2
    @1
    @2
    @1
    wi
    #
    @7
    @2
    @1
    biimt
    @8
    @2
    @1
    wn
    #
    wa
    @3
    @2
    @1
    iman
    wph
    @9
    @2
    notzfaus.2
    anbi2i
    xchbinxr
    syl6bb
    @1
    @3
    xor3
    sylibr
    eximii
    @4
    vx
    exnal
    mpbi
    nex
end
