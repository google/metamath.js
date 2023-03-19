include "crh.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "wf.mm"
include "rhmghm.mm"
include "ghmf.mm"
include "syl.mm"

theorem rhmf
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume rhmf.b: |- B = ( Base ` R )
  assume rhmf.c: |- C = ( Base ` S )


  assert |- ( F e. ( R RingHom S ) -> F : B --> C )

  proof
    cF
    cR
    cS
    crh
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
    rhmghm
    cR
    cS
    cF
    cB
    cC
    rhmf.b
    rhmf.c
    ghmf
    syl
end
