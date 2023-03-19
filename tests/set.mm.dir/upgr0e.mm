include "cumgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "umgr0e.mm"
include "umgrupgr.mm"
include "syl.mm"

theorem upgr0e
  let wph: wff ph
  let cG: class G
  let cW: class W
  let vx: setvar x
  assume umgr0e.g: |- ( ph -> G e. W )
  assume umgr0e.e: |- ( ph -> ( iEdg ` G ) = (/) )


  assert |- ( ph -> G e. UPGraph )

  proof
    wph
    cG
    cumgr
    wcel
    cG
    cupgr
    wcel
    wph
    cG
    cW
    umgr0e.g
    umgr0e.e
    umgr0e
    cG
    umgrupgr
    syl
end
