include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "covoln.mm"
include "cfv.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "ovnf.mm"
include "fdm.mm"
include "syl.mm"

theorem dmovn
  let wph: wff ph
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume dmovn.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> dom ( voln* ` X ) = ~P ( RR ^m X ) )

  proof
    wph
    cr
    cX
    cmap
    co
    cpw
    #
    cc0
    cpnf
    cicc
    co
    #
    cX
    covoln
    cfv
    #
    wf
    @2
    cdm
    @0
    wceq
    wph
    cX
    dmovn.1
    ovnf
    @0
    @1
    @2
    fdm
    syl
end
