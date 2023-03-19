include "cuni.mm"
include "covoln.mm"
include "cfv.mm"
include "ccaragen.mm"
include "cdm.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cvoln.mm"
include "wceq.mm"
include "a1i.mm"
include "dmvon.mm"
include "eqtrd.mm"
include "unieqd.mm"
include "ovnome.mm"
include "eqid.mm"
include "caragenuni.mm"
include "unidmovn.mm"
include "3eqtrd.mm"

theorem unidmvon
  let wph: wff ph
  let cS: class S
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume unidmvon.x: |- ( ph -> X e. Fin )
  assume unidmvon.s: |- S = dom ( voln ` X )


  assert |- ( ph -> U. S = ( RR ^m X ) )

  proof
    wph
    cS
    cuni
    cX
    covoln
    cfv
    #
    ccaragen
    cfv
    #
    cuni
    @0
    cdm
    cuni
    cr
    cX
    cmap
    co
    wph
    cS
    @1
    wph
    cS
    cX
    cvoln
    cfv
    cdm
    #
    @1
    cS
    @2
    wceq
    wph
    unidmvon.s
    a1i
    wph
    cX
    unidmvon.x
    dmvon
    eqtrd
    unieqd
    wph
    @1
    @0
    wph
    cX
    unidmvon.x
    ovnome
    @1
    eqid
    caragenuni
    wph
    cX
    unidmvon.x
    unidmovn
    3eqtrd
end
