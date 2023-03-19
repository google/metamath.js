include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cr.mm"
include "cfv.mm"
include "unitssre.mm"
include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "prob01.mm"
include "syl2anc.mm"
include "sseldi.mm"

theorem probvalrnd
  let wph: wff ph
  let cA: class A
  let cP: class P
  assume probmeasd.1: |- ( ph -> P e. Prob )
  assume probvalrnd.1: |- ( ph -> A e. dom P )


  assert |- ( ph -> ( P ` A ) e. RR )

  proof
    wph
    cc0
    c1
    cicc
    co
    #
    cr
    cA
    cP
    cfv
    #
    unitssre
    wph
    cP
    cprb
    wcel
    cA
    cP
    cdm
    wcel
    @1
    @0
    wcel
    probmeasd.1
    probvalrnd.1
    cA
    cP
    prob01
    syl2anc
    sseldi
end
