include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "crab.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "wsbc.mm"
include "rabsnifsb.mm"
include "sbcieg.mm"
include "ifbid.mm"
include "syl5eq.mm"
include "wn.mm"
include "rab0.mm"
include "ifid.mm"
include "eqtr4i.mm"
include "snprc.mm"
include "biimpi.mm"
include "rabeqdv.mm"
include "ifeq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem rabsnif
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rabsnif.f: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- { x e. { A } | ph } = if ( ps , { A } , (/) )

  proof
    cA
    cvv
    wcel
    #
    wph
    vx
    cA
    csn
    #
    crab
    #
    wps
    @1
    c0
    cif
    #
    wceq
    @0
    @2
    wph
    vx
    cA
    wsbc
    #
    @1
    c0
    cif
    @3
    wph
    vx
    cA
    rabsnifsb
    @0
    @4
    wps
    @1
    c0
    wph
    wps
    vx
    cA
    cvv
    rabsnif.f
    sbcieg
    ifbid
    syl5eq
    @0
    wn
    #
    wph
    vx
    c0
    crab
    #
    wps
    c0
    c0
    cif
    #
    @2
    @3
    @6
    c0
    @7
    wph
    vx
    rab0
    wps
    c0
    ifid
    eqtr4i
    @5
    wph
    vx
    @1
    c0
    @5
    @1
    c0
    wceq
    cA
    snprc
    biimpi
    #
    rabeqdv
    @5
    wps
    @1
    c0
    c0
    @8
    ifeq1d
    3eqtr4a
    pm2.61i
end
