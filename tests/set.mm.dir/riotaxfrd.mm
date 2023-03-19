include "wreu.mm"
include "wa.mm"
include "crio.mm"
include "cv.mm"
include "crab.mm"
include "wcel.mm"
include "rabid.mm"
include "baib.mm"
include "riotabiia.mm"
include "wceq.mm"
include "reuxfrd.mm"
include "riotacl2.mm"
include "adantl.mm"
include "wb.mm"
include "riotacl.mm"
include "nfriota1.mm"
include "rabxfrd.mm"
include "sylan2.mm"
include "mpbird.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"
include "syl5.mm"
include "baibr.mm"
include "reubiia.mm"
include "biimpi.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfel2.mm"
include "eleq1.mm"
include "riota2f.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "syl5eqr.mm"

theorem riotaxfrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume riotaxfrd.1: |- F/_ y C
  assume riotaxfrd.2: |- ( ( ph /\ y e. A ) -> B e. A )
  assume riotaxfrd.3: |- ( ( ph /\ ( iota_ y e. A ch ) e. A ) -> C e. A )
  assume riotaxfrd.4: |- ( x = B -> ( ps <-> ch ) )
  assume riotaxfrd.5: |- ( y = ( iota_ y e. A ch ) -> B = C )
  assume riotaxfrd.6: |- ( ( ph /\ x e. A ) -> E! y e. A x = B )

  disjoint B x
  disjoint C x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  assert |- ( ( ph /\ E! x e. A ps ) -> ( iota_ x e. A ps ) = C )

  proof
    wph
    wps
    vx
    cA
    wreu
    #
    wa
    #
    wps
    vx
    cA
    crio
    vx
    cv
    #
    wps
    vx
    cA
    crab
    #
    wcel
    #
    vx
    cA
    crio
    #
    cC
    @4
    wps
    vx
    cA
    @4
    @2
    cA
    wcel
    #
    wps
    wps
    vx
    cA
    rabid
    #
    baib
    riotabiia
    @1
    cC
    @3
    wcel
    #
    @5
    cC
    wceq
    #
    wph
    @0
    @8
    wph
    @0
    wch
    vy
    cA
    wreu
    #
    @8
    wph
    wps
    wch
    vx
    vy
    cB
    cA
    riotaxfrd.2
    riotaxfrd.6
    riotaxfrd.4
    reuxfrd
    #
    wph
    @10
    @8
    wph
    @10
    wa
    @8
    wch
    vy
    cA
    crio
    #
    wch
    vy
    cA
    crab
    wcel
    #
    @10
    @13
    wph
    wch
    vy
    cA
    riotacl2
    adantl
    @10
    wph
    @12
    cA
    wcel
    #
    @8
    @13
    wb
    wch
    vy
    cA
    riotacl
    #
    wph
    wps
    wch
    vx
    vy
    cB
    @12
    cC
    cA
    wch
    vy
    cA
    nfriota1
    riotaxfrd.1
    riotaxfrd.2
    riotaxfrd.4
    riotaxfrd.5
    rabxfrd
    sylan2
    mpbird
    ex
    sylbid
    imp
    @1
    cC
    cA
    wcel
    #
    @4
    vx
    cA
    wreu
    #
    @8
    @9
    wb
    wph
    @0
    @16
    wph
    @0
    @10
    @16
    @11
    @10
    @14
    wph
    @16
    @15
    wph
    @14
    @16
    riotaxfrd.3
    ex
    syl5
    sylbid
    imp
    @0
    @17
    wph
    @0
    @17
    wps
    @4
    vx
    cA
    @4
    @6
    wps
    @7
    baibr
    reubiia
    biimpi
    adantl
    @4
    @8
    vx
    cA
    cC
    vx
    cC
    nfcv
    vx
    cC
    @3
    wps
    vx
    cA
    nfrab1
    nfel2
    @2
    cC
    @3
    eleq1
    riota2f
    syl2anc
    mpbid
    syl5eqr
end
