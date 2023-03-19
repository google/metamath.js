include "wbr.mm"
include "ctcl.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "trclfvlb.mm"
include "syl.mm"
include "ssbrd.mm"
include "mpd.mm"

theorem frege91d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  assume frege91d.r: |- ( ph -> R e. _V )
  assume frege91d.ac: |- ( ph -> A R B )


  assert |- ( ph -> A ( t+ ` R ) B )

  proof
    wph
    cA
    cB
    cR
    wbr
    cA
    cB
    cR
    ctcl
    cfv
    #
    wbr
    frege91d.ac
    wph
    cR
    @0
    cA
    cB
    wph
    cR
    cvv
    wcel
    cR
    @0
    wss
    frege91d.r
    cR
    cvv
    trclfvlb
    syl
    ssbrd
    mpd
end
