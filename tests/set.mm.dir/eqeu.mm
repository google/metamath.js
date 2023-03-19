include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "wex.mm"
include "weq.mm"
include "weu.mm"
include "spcegv.mm"
include "imp.mm"
include "3adant3.mm"
include "eqeq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "3adant2.mm"
include "eu3v.mm"
include "sylanbrc.mm"

theorem eqeu
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume eqeu.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  disjoint ph y
  disjoint x y
  disjoint ps y
  disjoint A y
  assert |- ( ( A e. B /\ ps /\ A. x ( ph -> x = A ) ) -> E! x ph )

  proof
    cA
    cB
    wcel
    #
    wps
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wi
    #
    vx
    wal
    #
    w3a
    wph
    vx
    wex
    #
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    #
    wph
    vx
    weu
    @0
    wps
    @5
    @4
    @0
    wps
    @5
    wph
    wps
    vx
    cA
    cB
    eqeu.1
    spcegv
    imp
    3adant3
    @0
    @4
    @9
    wps
    @0
    @4
    @9
    @8
    @4
    vy
    cA
    cB
    vy
    cv
    #
    cA
    wceq
    #
    @7
    @3
    vx
    @11
    @6
    @2
    wph
    @10
    cA
    @1
    eqeq2
    imbi2d
    albidv
    spcegv
    imp
    3adant2
    wph
    vx
    vy
    eu3v
    sylanbrc
end
