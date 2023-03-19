include "cuni.mm"
include "cdm.mm"
include "come.mm"
include "wcel.mm"
include "wss.mm"
include "caragenss.mm"
include "syl.mm"
include "unissd.mm"
include "eqid.mm"
include "caragenunidm.mm"
include "elssuni.mm"
include "eqssd.mm"

theorem caragenuni
  let wph: wff ph
  let cS: class S
  let cO: class O
  let vk: setvar k
  let vx: setvar x
  assume caragenuni.o: |- ( ph -> O e. OutMeas )
  assume caragenuni.s: |- S = ( CaraGen ` O )


  assert |- ( ph -> U. S = U. dom O )

  proof
    wph
    cS
    cuni
    #
    cO
    cdm
    #
    cuni
    #
    wph
    cS
    @1
    wph
    cO
    come
    wcel
    cS
    @1
    wss
    caragenuni.o
    cS
    cO
    caragenuni.s
    caragenss
    syl
    unissd
    wph
    @2
    cS
    wcel
    @2
    @0
    wss
    wph
    cS
    cO
    @2
    caragenuni.o
    @2
    eqid
    caragenuni.s
    caragenunidm
    @2
    cS
    elssuni
    syl
    eqssd
end
