include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cun.mm"
include "cfn.mm"
include "wcel.mm"
include "wfun.mm"
include "wa.mm"
include "wi.mm"
include "fsuppimp.mm"
include "unfi.mm"
include "expcom.mm"
include "adantl.mm"
include "3syl.mm"
include "com12.mm"
include "syl.mm"
include "mpcom.mm"

theorem fsuppunfi
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cZ: class Z
  assume fsuppun.f: |- ( ph -> F finSupp Z )
  assume fsuppun.g: |- ( ph -> G finSupp Z )


  assert |- ( ph -> ( ( F supp Z ) u. ( G supp Z ) ) e. Fin )

  proof
    cF
    cZ
    cfsupp
    wbr
    #
    wph
    cF
    cZ
    csupp
    co
    #
    cG
    cZ
    csupp
    co
    #
    cun
    cfn
    wcel
    #
    fsuppun.f
    @0
    cF
    wfun
    #
    @1
    cfn
    wcel
    #
    wa
    wph
    @3
    wi
    #
    cF
    cZ
    fsuppimp
    @5
    @6
    @4
    wph
    @5
    @3
    wph
    cG
    cZ
    cfsupp
    wbr
    cG
    wfun
    #
    @2
    cfn
    wcel
    #
    wa
    @5
    @3
    wi
    #
    fsuppun.g
    cG
    cZ
    fsuppimp
    @8
    @9
    @7
    @5
    @8
    @3
    @1
    @2
    unfi
    expcom
    adantl
    3syl
    com12
    adantl
    syl
    mpcom
end
