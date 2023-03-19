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
include "df-rmo.mm"
include "ralbii.mm"
include "sylbir.mm"
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

theorem reuxfr2d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume reuxfr2d.1: |- ( ( ph /\ y e. B ) -> A e. B )
  assume reuxfr2d.2: |- ( ( ph /\ x e. B ) -> E* y e. B x = A )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint A x
  disjoint B x
  disjoint B y
  assert |- ( ph -> ( E! x e. B E. y e. B ( x = A /\ ps ) <-> E! y e. B ps ) )

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
    cB
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
    cB
    wreu
    #
    wps
    vy
    cB
    wreu
    wph
    @3
    @5
    wph
    @2
    vy
    cB
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
    cB
    wrmo
    #
    @6
    @8
    @1
    vy
    cB
    wrmo
    @10
    reuxfr2d.2
    @1
    wps
    vy
    cB
    rmoan
    syl
    @9
    @2
    vy
    cB
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
    cB
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
    #
    vy
    cB
    @12
    vy
    cB
    wral
    @2
    vx
    cB
    wrmo
    #
    vy
    cB
    wral
    @13
    @14
    @12
    vy
    cB
    @2
    vx
    cB
    df-rmo
    ralbii
    @2
    vy
    vx
    cB
    cB
    2reuswap
    sylbir
    @12
    vy
    cv
    cB
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
    @16
    vx
    vx
    cA
    moeq
    moani
    @17
    @11
    vx
    @17
    @1
    @16
    wa
    @11
    @16
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
    cB
    wph
    @15
    wa
    cA
    cB
    wcel
    @4
    wps
    wb
    reuxfr2d.1
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
