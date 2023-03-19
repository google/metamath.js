include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "clmhm.mm"
include "wf1o.mm"
include "islmim.mm"
include "simprbi.mm"

theorem lmimf1o
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume islmim.b: |- B = ( Base ` R )
  assume islmim.c: |- C = ( Base ` S )


  assert |- ( F e. ( R LMIso S ) -> F : B -1-1-onto-> C )

  proof
    cF
    cR
    cS
    clmim
    co
    wcel
    cF
    cR
    cS
    clmhm
    co
    wcel
    cB
    cC
    cF
    wf1o
    cB
    cC
    cR
    cS
    cF
    islmim.b
    islmim.c
    islmim
    simprbi
end
