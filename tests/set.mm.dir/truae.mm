include "crab.mm"
include "cae.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "pm2.24d.mm"
include "ralrimivw.mm"
include "rabss.mm"
include "sylibr.mm"
include "ss0.mm"
include "syl.mm"
include "fveq2d.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "cdm.mm"
include "measbasedom.mm"
include "measvnul.mm"
include "sylbi.mm"
include "eqtrd.mm"
include "wb.mm"
include "braew.mm"
include "mpbird.mm"

theorem truae
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cM: class M
  let cO: class O
  assume truae.1: |- U. dom M = O
  assume truae.2: |- ( ph -> M e. U. ran measures )
  assume truae.3: |- ( ph -> ps )

  disjoint O x
  disjoint ph x
  assert |- ( ph -> { x e. O | ps } ae M )

  proof
    wph
    wps
    vx
    cO
    crab
    cM
    cae
    wbr
    #
    wps
    wn
    #
    vx
    cO
    crab
    #
    cM
    cfv
    #
    cc0
    wceq
    #
    wph
    @3
    c0
    cM
    cfv
    #
    cc0
    wph
    @2
    c0
    cM
    wph
    @2
    c0
    wss
    #
    @2
    c0
    wceq
    wph
    @1
    vx
    cv
    c0
    wcel
    #
    wi
    #
    vx
    cO
    wral
    @6
    wph
    @8
    vx
    cO
    wph
    wps
    @7
    truae.3
    pm2.24d
    ralrimivw
    @1
    vx
    cO
    c0
    rabss
    sylibr
    @2
    ss0
    syl
    fveq2d
    wph
    cM
    cmeas
    crn
    cuni
    wcel
    #
    @5
    cc0
    wceq
    #
    truae.2
    @9
    cM
    cM
    cdm
    #
    cmeas
    cfv
    wcel
    @10
    cM
    measbasedom
    @11
    cM
    measvnul
    sylbi
    syl
    eqtrd
    wph
    @9
    @0
    @4
    wb
    truae.2
    wps
    vx
    cM
    cO
    truae.1
    braew
    syl
    mpbird
end
