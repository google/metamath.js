include "covoln.mm"
include "cfv.mm"
include "cdm.mm"
include "cuni.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "dmovn.mm"
include "unieqd.mm"
include "wceq.mm"
include "unipw.mm"
include "a1i.mm"
include "eqtrd.mm"

theorem unidmovn
  let wph: wff ph
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume unidmovn.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> U. dom ( voln* ` X ) = ( RR ^m X ) )

  proof
    wph
    cX
    covoln
    cfv
    cdm
    #
    cuni
    cr
    cX
    cmap
    co
    #
    cpw
    #
    cuni
    #
    @1
    wph
    @0
    @2
    wph
    cX
    unidmovn.1
    dmovn
    unieqd
    @3
    @1
    wceq
    wph
    @1
    unipw
    a1i
    eqtrd
end
