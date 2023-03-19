include "ctp.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "an3andi.mm"
include "a1i.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "expcom.mm"
include "pm5.32d.mm"
include "raltpg.mm"
include "syl3anc.mm"
include "c0.mm"
include "wne.mm"
include "tpnzd.mm"
include "r19.28zv.mm"
include "syl.mm"
include "3bitr2d.mm"
include "bianabs.mm"
include "bicomd.mm"

theorem raltpd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  assume ralprd.1: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )
  assume ralprd.2: |- ( ( ph /\ x = B ) -> ( ps <-> th ) )
  assume raltpd.3: |- ( ( ph /\ x = C ) -> ( ps <-> ta ) )
  assume ralprd.a: |- ( ph -> A e. V )
  assume ralprd.b: |- ( ph -> B e. W )
  assume raltpd.c: |- ( ph -> C e. X )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint ch x
  disjoint th x
  disjoint ta x
  assert |- ( ph -> ( A. x e. { A , B , C } ps <-> ( ch /\ th /\ ta ) ) )

  proof
    wph
    wps
    vx
    cA
    cB
    cC
    ctp
    #
    wral
    #
    wch
    wth
    wta
    w3a
    #
    wph
    wph
    @2
    wa
    #
    @1
    wph
    @3
    @1
    wph
    @3
    wph
    wch
    wa
    #
    wph
    wth
    wa
    #
    wph
    wta
    wa
    #
    w3a
    #
    wph
    wps
    wa
    #
    vx
    @0
    wral
    #
    wph
    @1
    wa
    #
    @3
    @7
    wb
    wph
    wph
    wch
    wth
    wta
    an3andi
    a1i
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    cC
    cX
    wcel
    @9
    @7
    wb
    ralprd.a
    ralprd.b
    raltpd.c
    @8
    @4
    @5
    @6
    vx
    cA
    cB
    cC
    cV
    cW
    cX
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wps
    wch
    wph
    @12
    wps
    wch
    wb
    ralprd.1
    expcom
    pm5.32d
    @11
    cB
    wceq
    #
    wph
    wps
    wth
    wph
    @13
    wps
    wth
    wb
    ralprd.2
    expcom
    pm5.32d
    @11
    cC
    wceq
    #
    wph
    wps
    wta
    wph
    @14
    wps
    wta
    wb
    raltpd.3
    expcom
    pm5.32d
    raltpg
    syl3anc
    wph
    @0
    c0
    wne
    @9
    @10
    wb
    wph
    cA
    cB
    cC
    cV
    ralprd.a
    tpnzd
    wph
    wps
    vx
    @0
    r19.28zv
    syl
    3bitr2d
    bianabs
    bicomd
    bianabs
end
