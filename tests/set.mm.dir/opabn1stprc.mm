include "wex.mm"
include "copab.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "cdm.mm"
include "cv.mm"
include "wa.mm"
include "vex.mm"
include "biantrur.mm"
include "opabbii.mm"
include "dmeqi.mm"
include "wral.mm"
include "wceq.mm"
include "id.mm"
include "ralrimivw.mm"
include "dmopab3.mm"
include "sylib.mm"
include "syl5eq.mm"
include "vprc.mm"
include "a1i.mm"
include "eqneltrd.mm"
include "dmexg.mm"
include "nsyl.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem opabn1stprc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph x
  assert |- ( E. y ph -> { <. x , y >. | ph } e/ _V )

  proof
    wph
    vy
    wex
    #
    wph
    vx
    vy
    copab
    #
    cvv
    wcel
    #
    wn
    @1
    cvv
    wnel
    @0
    @1
    cdm
    #
    cvv
    wcel
    @2
    @0
    @3
    cvv
    cvv
    @0
    @3
    vx
    cv
    cvv
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    #
    cdm
    #
    cvv
    @1
    @6
    wph
    @5
    vx
    vy
    @4
    wph
    vx
    vex
    biantrur
    opabbii
    dmeqi
    @0
    @0
    vx
    cvv
    wral
    @7
    cvv
    wceq
    @0
    @0
    vx
    cvv
    @0
    id
    ralrimivw
    wph
    vx
    vy
    cvv
    dmopab3
    sylib
    syl5eq
    cvv
    cvv
    wcel
    wn
    @0
    vprc
    a1i
    eqneltrd
    @1
    cvv
    dmexg
    nsyl
    @1
    cvv
    df-nel
    sylibr
end
