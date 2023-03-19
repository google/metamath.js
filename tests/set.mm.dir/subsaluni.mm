include "crest.mm"
include "co.mm"
include "cuni.mm"
include "csalg.mm"
include "restuni4.mm"
include "eqcomd.mm"
include "cvv.mm"
include "uniexd.mm"
include "ssexd.mm"
include "eqid.mm"
include "subsalsal.mm"
include "salunid.mm"
include "eqeltrd.mm"

theorem subsaluni
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vx: setvar x
  assume subsaluni.1: |- ( ph -> S e. SAlg )
  assume subsaluni.2: |- ( ph -> A C_ U. S )


  assert |- ( ph -> A e. ( S |`t A ) )

  proof
    wph
    cA
    cS
    cA
    crest
    co
    #
    cuni
    #
    @0
    wph
    @1
    cA
    wph
    cS
    cA
    csalg
    subsaluni.1
    subsaluni.2
    restuni4
    eqcomd
    wph
    @0
    wph
    cA
    cS
    @0
    cvv
    subsaluni.1
    wph
    cA
    cS
    cuni
    cvv
    wph
    cS
    csalg
    subsaluni.1
    uniexd
    subsaluni.2
    ssexd
    @0
    eqid
    subsalsal
    salunid
    eqeltrd
end
