include "cdm.mm"
include "cuni.mm"
include "unveldomd.mm"
include "probvalrnd.mm"

theorem probtotrnd
  let wph: wff ph
  let cP: class P
  assume probmeasd.1: |- ( ph -> P e. Prob )


  assert |- ( ph -> ( P ` U. dom P ) e. RR )

  proof
    wph
    cP
    cdm
    cuni
    cP
    probmeasd.1
    wph
    cP
    probmeasd.1
    unveldomd
    probvalrnd
end
