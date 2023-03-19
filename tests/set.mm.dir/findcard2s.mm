include "cv.mm"
include "cfn.mm"
include "wcel.mm"
include "wi.mm"
include "wn.mm"
include "ex.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "uncom.mm"
include "wss.mm"
include "snssi.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5reqr.mm"
include "vex.mm"
include "eqvinc.mm"
include "bicomd.mm"
include "sylan9bb.mm"
include "exlimiv.mm"
include "syl.mm"
include "biimpd.mm"
include "pm2.61d2.mm"
include "findcard2.mm"

theorem findcard2s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume findcard2s.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume findcard2s.2: |- ( x = y -> ( ph <-> ch ) )
  assume findcard2s.3: |- ( x = ( y u. { z } ) -> ( ph <-> th ) )
  assume findcard2s.4: |- ( x = A -> ( ph <-> ta ) )
  assume findcard2s.5: |- ps
  assume findcard2s.6: |- ( ( y e. Fin /\ -. z e. y ) -> ( ch -> th ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ch x
  disjoint ph y
  disjoint ph z
  disjoint ps x
  disjoint ta x
  disjoint th x
  assert |- ( A e. Fin -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    vx
    vy
    vz
    cA
    findcard2s.1
    findcard2s.2
    findcard2s.3
    findcard2s.4
    findcard2s.5
    vy
    cv
    #
    cfn
    wcel
    #
    vz
    cv
    #
    @0
    wcel
    #
    wch
    wth
    wi
    #
    @1
    @3
    wn
    @4
    findcard2s.6
    ex
    @3
    wch
    wth
    @3
    vx
    cv
    #
    @0
    wceq
    #
    @5
    @0
    @2
    csn
    #
    cun
    #
    wceq
    #
    wa
    #
    vx
    wex
    #
    wch
    wth
    wb
    #
    @3
    @0
    @8
    wceq
    @11
    @3
    @8
    @7
    @0
    cun
    #
    @0
    @7
    @0
    uncom
    @3
    @7
    @0
    wss
    @13
    @0
    wceq
    @2
    @0
    snssi
    @7
    @0
    ssequn1
    sylib
    syl5reqr
    vx
    @0
    @8
    vy
    vex
    eqvinc
    sylib
    @10
    @12
    vx
    @6
    wch
    wph
    @9
    wth
    @6
    wph
    wch
    findcard2s.2
    bicomd
    findcard2s.3
    sylan9bb
    exlimiv
    syl
    biimpd
    pm2.61d2
    findcard2
end
