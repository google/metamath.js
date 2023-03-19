include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "wrmo.mm"
include "wral.mm"
include "wi.mm"
include "wcel.mm"
include "rmoan.mm"
include "syl.mm"
include "ancom.mm"
include "rmobii.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "2reuswap.mm"
include "wmo.mm"
include "2reuswap2.mm"
include "moeq.mm"
include "moani.mm"
include "an12.mm"
include "bitri.mm"
include "mobii.mm"
include "mpbi.mm"
include "a1i.mm"
include "mprg.mm"
include "impbid1.mm"
include "wb.mm"
include "biidd.mm"
include "ceqsrexv.mm"
include "reubidva.mm"
include "bitrd.mm"

theorem reuxfr3d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume reuxfr3d.1: |- ( ( ph /\ y e. C ) -> A e. B )
  assume reuxfr3d.2: |- ( ( ph /\ x e. B ) -> E* y e. C x = A )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint A x
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ph -> ( E! x e. B E. y e. C ( x = A /\ ps ) <-> E! y e. C ps ) )

  proof
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wps
    wa
    #
    vy
    cC
    wrex
    vx
    cB
    wreu
    #
    @2
    vx
    cB
    wrex
    #
    vy
    cC
    wreu
    #
    wps
    vy
    cC
    wreu
    wph
    @3
    @5
    wph
    @2
    vy
    cC
    wrmo
    #
    vx
    cB
    wral
    @3
    @5
    wi
    wph
    @6
    vx
    cB
    wph
    @0
    cB
    wcel
    #
    wa
    #
    wps
    @1
    wa
    #
    vy
    cC
    wrmo
    #
    @6
    @8
    @1
    vy
    cC
    wrmo
    @10
    reuxfr3d.2
    @1
    wps
    vy
    cC
    rmoan
    syl
    @9
    @2
    vy
    cC
    wps
    @1
    ancom
    rmobii
    sylib
    ralrimiva
    @2
    vx
    vy
    cB
    cC
    2reuswap
    syl
    @7
    @2
    wa
    #
    vx
    wmo
    #
    @5
    @3
    wi
    vy
    cC
    @2
    vy
    vx
    cC
    cB
    2reuswap2
    @12
    vy
    cv
    cC
    wcel
    #
    @7
    wps
    wa
    #
    @1
    wa
    #
    vx
    wmo
    @12
    @1
    @14
    vx
    vx
    cA
    moeq
    moani
    @15
    @11
    vx
    @15
    @1
    @14
    wa
    @11
    @14
    @1
    ancom
    @1
    @7
    wps
    an12
    bitri
    mobii
    mpbi
    a1i
    mprg
    impbid1
    wph
    @4
    wps
    vy
    cC
    wph
    @13
    wa
    cA
    cB
    wcel
    @4
    wps
    wb
    reuxfr3d.1
    wps
    wps
    vx
    cA
    cB
    @1
    wps
    biidd
    ceqsrexv
    syl
    reubidva
    bitrd
end
