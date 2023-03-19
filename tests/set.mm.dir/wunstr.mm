include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "wunrn.mm"
include "wununi.mm"
include "wss.mm"
include "strfvss.mm"
include "a1i.mm"
include "wunss.mm"

theorem wunstr
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cE: class E
  let cN: class N
  assume ndxarg.1: |- E = Slot N
  assume wunstr.2: |- ( ph -> U e. WUni )
  assume wunstr.3: |- ( ph -> S e. U )


  assert |- ( ph -> ( E ` S ) e. U )

  proof
    wph
    cS
    crn
    #
    cuni
    #
    cS
    cE
    cfv
    #
    cU
    wunstr.2
    wph
    @0
    cU
    wunstr.2
    wph
    cS
    cU
    wunstr.2
    wunstr.3
    wunrn
    wununi
    @2
    @1
    wss
    wph
    cS
    cE
    cN
    ndxarg.1
    strfvss
    a1i
    wunss
end
