include "csn.mm"
include "wfn.mm"
include "wcel.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "cres.mm"
include "fnresdm.mm"
include "wfun.mm"
include "wss.mm"
include "fnfun.mm"
include "funressn.mm"
include "syl.mm"
include "eqsstr3d.mm"
include "sseld.mm"
include "elsni.mm"
include "syl6.mm"

theorem fnsnr
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F Fn { A } -> ( B e. F -> B = <. A , ( F ` A ) >. ) )

  proof
    cF
    cA
    csn
    #
    wfn
    #
    cB
    cF
    wcel
    cB
    cA
    cA
    cF
    cfv
    cop
    #
    csn
    #
    wcel
    cB
    @2
    wceq
    @1
    cF
    @3
    cB
    @1
    cF
    cF
    @0
    cres
    #
    @3
    @0
    cF
    fnresdm
    @1
    cF
    wfun
    @4
    @3
    wss
    @0
    cF
    fnfun
    cA
    cF
    funressn
    syl
    eqsstr3d
    sseld
    cB
    @2
    elsni
    syl6
end
