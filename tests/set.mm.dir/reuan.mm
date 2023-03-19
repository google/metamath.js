include "wa.mm"
include "wreu.mm"
include "wrex.mm"
include "wrmo.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "simpl.mm"
include "a1i.mm"
include "rexlimi.mm"
include "adantr.mm"
include "simpr.mm"
include "reximi.mm"
include "nfre1.mm"
include "a1d.mm"
include "ancrd.mm"
include "impbid2.mm"
include "rmobida.mm"
include "biimpa.mm"
include "jca32.mm"
include "reu5.mm"
include "anbi2i.mm"
include "3imtr4i.mm"
include "wb.mm"
include "ibar.mm"
include "reubida.mm"
include "impbii.mm"

theorem reuan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vk: setvar k
  assume rmoanim.1: |- F/ x ph

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  disjoint ps y
  disjoint k x
  assert |- ( E! x e. A ( ph /\ ps ) <-> ( ph /\ E! x e. A ps ) )

  proof
    wph
    wps
    wa
    #
    vx
    cA
    wreu
    #
    wph
    wps
    vx
    cA
    wreu
    #
    wa
    #
    @0
    vx
    cA
    wrex
    #
    @0
    vx
    cA
    wrmo
    #
    wa
    #
    wph
    wps
    vx
    cA
    wrex
    #
    wps
    vx
    cA
    wrmo
    #
    wa
    #
    wa
    @1
    @3
    @6
    wph
    @7
    @8
    @4
    wph
    @5
    @0
    wph
    vx
    cA
    rmoanim.1
    @0
    wph
    wi
    vx
    cv
    cA
    wcel
    #
    wph
    wps
    simpl
    a1i
    rexlimi
    #
    adantr
    @4
    @7
    @5
    @0
    wps
    vx
    cA
    wph
    wps
    simpr
    #
    reximi
    adantr
    @4
    @5
    @8
    @4
    @0
    wps
    vx
    cA
    @0
    vx
    cA
    nfre1
    @4
    @10
    wa
    #
    @0
    wps
    @12
    @13
    wps
    wph
    @13
    wph
    wps
    @4
    wph
    @10
    @11
    adantr
    a1d
    ancrd
    impbid2
    rmobida
    biimpa
    jca32
    @0
    vx
    cA
    reu5
    @2
    @9
    wph
    wps
    vx
    cA
    reu5
    anbi2i
    3imtr4i
    wph
    @2
    @1
    wph
    wps
    @0
    vx
    cA
    rmoanim.1
    wph
    wps
    @0
    wb
    @10
    wph
    wps
    ibar
    adantr
    reubida
    biimpa
    impbii
end
