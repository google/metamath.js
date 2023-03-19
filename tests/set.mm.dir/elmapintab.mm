include "wcel.mm"
include "cfv.mm"
include "cab.mm"
include "cint.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "fvex.mm"
include "elintab.mm"
include "anbi2i.mm"
include "baibr.mm"
include "imbi2d.mm"
include "albidv.mm"
include "pm5.32i.mm"
include "3bitri.mm"

theorem elmapintab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cF: class F
  assume elmapintab.1: |- ( A e. B <-> ( A e. C /\ ( F ` A ) e. |^| { x | ph } ) )
  assume elmapintab.2: |- ( A e. E <-> ( A e. C /\ ( F ` A ) e. x ) )

  disjoint A x
  disjoint C x
  disjoint F x
  assert |- ( A e. B <-> ( A e. C /\ A. x ( ph -> A e. E ) ) )

  proof
    cA
    cB
    wcel
    cA
    cC
    wcel
    #
    cA
    cF
    cfv
    #
    wph
    vx
    cab
    cint
    wcel
    #
    wa
    @0
    wph
    @1
    vx
    cv
    wcel
    #
    wi
    #
    vx
    wal
    #
    wa
    @0
    wph
    cA
    cE
    wcel
    #
    wi
    #
    vx
    wal
    #
    wa
    elmapintab.1
    @2
    @5
    @0
    wph
    vx
    @1
    cA
    cF
    fvex
    elintab
    anbi2i
    @0
    @5
    @8
    @0
    @4
    @7
    vx
    @0
    @3
    @6
    wph
    @6
    @0
    @3
    elmapintab.2
    baibr
    imbi2d
    albidv
    pm5.32i
    3bitri
end
