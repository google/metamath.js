include "crngh.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "wf.mm"
include "rnghmghm.mm"
include "ghmf.mm"
include "syl.mm"

theorem rnghmf
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume rnghmf.b: |- B = ( Base ` R )
  assume rnghmf.c: |- C = ( Base ` S )


  assert |- ( F e. ( R RngHomo S ) -> F : B --> C )

  proof
    cF
    cR
    cS
    crngh
    co
    wcel
    cF
    cR
    cS
    cghm
    co
    wcel
    cB
    cC
    cF
    wf
    cR
    cS
    cF
    rnghmghm
    cR
    cS
    cF
    cB
    cC
    rnghmf.b
    rnghmf.c
    ghmf
    syl
end
