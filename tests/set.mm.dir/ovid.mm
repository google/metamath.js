include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cop.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "df-ov.mm"
include "eqeq1i.mm"
include "copab.mm"
include "wfn.mm"
include "wb.mm"
include "coprab.mm"
include "fnoprab.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "opabid.mm"
include "biimpri.mm"
include "fnopfvb.mm"
include "sylancr.mm"
include "eleq2i.mm"
include "oprabid.mm"
include "bitri.mm"
include "baib.mm"
include "bitrd.mm"
include "syl5bb.mm"

theorem ovid
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cF: class F
  assume ovid.1: |- ( ( x e. R /\ y e. S ) -> E! z ph )
  assume ovid.2: |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) }

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint S z
  assert |- ( ( x e. R /\ y e. S ) -> ( ( x F y ) = z <-> ph ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    vz
    cv
    #
    wceq
    @0
    @1
    cop
    #
    cF
    cfv
    #
    @3
    wceq
    #
    @0
    cR
    wcel
    @1
    cS
    wcel
    wa
    #
    wph
    @2
    @5
    @3
    @0
    @1
    cF
    df-ov
    eqeq1i
    @7
    @6
    @4
    @3
    cop
    #
    cF
    wcel
    #
    wph
    @7
    cF
    @7
    vx
    vy
    copab
    #
    wfn
    #
    @4
    @10
    wcel
    #
    @6
    @9
    wb
    @11
    @7
    wph
    wa
    #
    vx
    vy
    vz
    coprab
    #
    @10
    wfn
    @7
    wph
    vx
    vy
    vz
    ovid.1
    fnoprab
    @10
    cF
    @14
    ovid.2
    fneq1i
    mpbir
    @12
    @7
    @7
    vx
    vy
    opabid
    biimpri
    @10
    @4
    @3
    cF
    fnopfvb
    sylancr
    @9
    @7
    wph
    @9
    @8
    @14
    wcel
    @13
    cF
    @14
    @8
    ovid.2
    eleq2i
    @13
    vx
    vy
    vz
    oprabid
    bitri
    baib
    bitrd
    syl5bb
end
