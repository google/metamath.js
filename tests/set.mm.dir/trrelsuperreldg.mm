include "wss.mm"
include "ccom.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wrel.mm"
include "relssdmrn.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "xptrrel.mm"
include "a1i.mm"
include "coeq12d.mm"
include "3sstr4d.mm"
include "jca.mm"

theorem trrelsuperreldg
  let wph: wff ph
  let cR: class R
  let cS: class S
  assume trrelsuperreldg.r: |- ( ph -> Rel R )
  assume trrelsuperreldg.s: |- ( ph -> S = ( dom R X. ran R ) )


  assert |- ( ph -> ( R C_ S /\ ( S o. S ) C_ S ) )

  proof
    wph
    cR
    cS
    wss
    cS
    cS
    ccom
    #
    cS
    wss
    wph
    cR
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    #
    cS
    wph
    cR
    wrel
    cR
    @3
    wss
    trrelsuperreldg.r
    cR
    relssdmrn
    syl
    trrelsuperreldg.s
    sseqtr4d
    wph
    @3
    @3
    ccom
    #
    @3
    @0
    cS
    @4
    @3
    wss
    wph
    @1
    @2
    xptrrel
    a1i
    wph
    cS
    @3
    cS
    @3
    trrelsuperreldg.s
    trrelsuperreldg.s
    coeq12d
    trrelsuperreldg.s
    3sstr4d
    jca
end
