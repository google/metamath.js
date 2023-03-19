include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cvoln.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "covoln.mm"
include "cuni.mm"
include "ccaragen.mm"
include "ovnome.mm"
include "eqid.mm"
include "caragenunidm.mm"
include "cpw.mm"
include "dmovn.mm"
include "unieqd.mm"
include "wceq.mm"
include "unipw.mm"
include "a1i.mm"
include "eqtr2d.mm"
include "dmvon.mm"
include "eleq12d.mm"
include "mpbird.mm"

theorem rrnmbl
  let wph: wff ph
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume rrnmbl.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> ( RR ^m X ) e. dom ( voln ` X ) )

  proof
    wph
    cr
    cX
    cmap
    co
    #
    cX
    cvoln
    cfv
    cdm
    #
    wcel
    cX
    covoln
    cfv
    #
    cdm
    #
    cuni
    #
    @2
    ccaragen
    cfv
    #
    wcel
    wph
    @5
    @2
    @4
    wph
    cX
    rrnmbl.1
    ovnome
    @4
    eqid
    @5
    eqid
    caragenunidm
    wph
    @0
    @4
    @1
    @5
    wph
    @4
    @0
    cpw
    #
    cuni
    #
    @0
    wph
    @3
    @6
    wph
    cX
    rrnmbl.1
    dmovn
    unieqd
    @7
    @0
    wceq
    wph
    @0
    unipw
    a1i
    eqtr2d
    wph
    cX
    rrnmbl.1
    dmvon
    eleq12d
    mpbird
end
