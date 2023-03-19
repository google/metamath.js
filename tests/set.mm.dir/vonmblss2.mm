include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "cvoln.mm"
include "cfv.mm"
include "cdm.mm"
include "vonmblss.mm"
include "sseldd.mm"
include "elpwi.mm"
include "syl.mm"

theorem vonmblss2
  let wph: wff ph
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume vonmblss2.x: |- ( ph -> X e. Fin )
  assume vonmblss2.y: |- ( ph -> Y e. dom ( voln ` X ) )


  assert |- ( ph -> Y C_ ( RR ^m X ) )

  proof
    wph
    cY
    cr
    cX
    cmap
    co
    #
    cpw
    #
    wcel
    cY
    @0
    wss
    wph
    cX
    cvoln
    cfv
    cdm
    @1
    cY
    wph
    cX
    vonmblss2.x
    vonmblss
    vonmblss2.y
    sseldd
    cY
    @0
    elpwi
    syl
end
