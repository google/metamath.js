include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wi.mm"
include "wal.mm"
include "adantld.mm"
include "alrimiv.mm"
include "pm5.3.mm"
include "albii.mm"
include "ss2ab.mm"
include "bitr4i.mm"
include "sylib.mm"
include "intss.mm"
include "syl.mm"

theorem clss2lem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cX: class X
  assume clss2lem.1: |- ( ph -> ( ch -> ps ) )

  disjoint ph x
  assert |- ( ph -> |^| { x | ( X C_ x /\ ps ) } C_ |^| { x | ( X C_ x /\ ch ) } )

  proof
    wph
    cX
    vx
    cv
    wss
    #
    wch
    wa
    #
    vx
    cab
    #
    @0
    wps
    wa
    #
    vx
    cab
    #
    wss
    #
    @4
    cint
    @2
    cint
    wss
    wph
    @1
    wps
    wi
    #
    vx
    wal
    #
    @5
    wph
    @6
    vx
    wph
    wch
    wps
    @0
    clss2lem.1
    adantld
    alrimiv
    @7
    @1
    @3
    wi
    #
    vx
    wal
    @5
    @6
    @8
    vx
    @0
    wch
    wps
    pm5.3
    albii
    @1
    @3
    vx
    ss2ab
    bitr4i
    sylib
    @2
    @4
    intss
    syl
end
