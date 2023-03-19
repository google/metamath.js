include "cvoln.mm"
include "cfv.mm"
include "cdm.mm"
include "covoln.mm"
include "ccaragen.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "dmvon.mm"
include "come.mm"
include "wcel.mm"
include "wss.mm"
include "ovnome.mm"
include "eqid.mm"
include "caragenss.mm"
include "syl.mm"
include "dmovn.mm"
include "sseqtrd.mm"
include "eqsstrd.mm"

theorem vonmblss
  let wph: wff ph
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume vonmblss.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> dom ( voln ` X ) C_ ~P ( RR ^m X ) )

  proof
    wph
    cX
    cvoln
    cfv
    cdm
    cX
    covoln
    cfv
    #
    ccaragen
    cfv
    #
    cr
    cX
    cmap
    co
    cpw
    #
    wph
    cX
    vonmblss.1
    dmvon
    wph
    @1
    @0
    cdm
    #
    @2
    wph
    @0
    come
    wcel
    @1
    @3
    wss
    wph
    cX
    vonmblss.1
    ovnome
    @1
    @0
    @1
    eqid
    caragenss
    syl
    wph
    cX
    vonmblss.1
    dmovn
    sseqtrd
    eqsstrd
end
