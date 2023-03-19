include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "wf.mm"
include "lmghm.mm"
include "ghmf.mm"
include "syl.mm"

theorem lmhmf
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  assume lmhmf.b: |- B = ( Base ` S )
  assume lmhmf.c: |- C = ( Base ` T )


  assert |- ( F e. ( S LMHom T ) -> F : B --> C )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    cF
    cS
    cT
    cghm
    co
    wcel
    cB
    cC
    cF
    wf
    cS
    cT
    cF
    lmghm
    cS
    cT
    cF
    cB
    cC
    lmhmf.b
    lmhmf.c
    ghmf
    syl
end
