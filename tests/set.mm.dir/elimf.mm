include "wf.mm"
include "cif.mm"
include "feq1.mm"
include "elimhyp.mm"

theorem elimf
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume elimf.1: |- G : A --> B


  assert |- if ( F : A --> B , F , G ) : A --> B

  proof
    cA
    cB
    cF
    wf
    #
    cA
    cB
    @0
    cF
    cG
    cif
    #
    wf
    cA
    cB
    cG
    wf
    cF
    cG
    cA
    cB
    cF
    @1
    feq1
    cA
    cB
    cG
    @1
    feq1
    elimf.1
    elimhyp
end
