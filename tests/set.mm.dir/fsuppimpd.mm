include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wfun.mm"
include "fsuppimp.mm"
include "simprd.mm"
include "syl.mm"

theorem fsuppimpd
  let wph: wff ph
  let cF: class F
  let cZ: class Z
  assume fsuppimpd.f: |- ( ph -> F finSupp Z )


  assert |- ( ph -> ( F supp Z ) e. Fin )

  proof
    wph
    cF
    cZ
    cfsupp
    wbr
    #
    cF
    cZ
    csupp
    co
    cfn
    wcel
    #
    fsuppimpd.f
    @0
    cF
    wfun
    @1
    cF
    cZ
    fsuppimp
    simprd
    syl
end
