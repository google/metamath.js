include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "wf1o.mm"
include "isgim.mm"
include "simprbi.mm"

theorem gimf1o
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume isgim.b: |- B = ( Base ` R )
  assume isgim.c: |- C = ( Base ` S )


  assert |- ( F e. ( R GrpIso S ) -> F : B -1-1-onto-> C )

  proof
    cF
    cR
    cS
    cgim
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
    wf1o
    cB
    cC
    cR
    cS
    cF
    isgim.b
    isgim.c
    isgim
    simprbi
end
