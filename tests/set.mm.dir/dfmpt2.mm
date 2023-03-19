include "cmpt2.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csb.mm"
include "cmpt.mm"
include "cop.mm"
include "csn.mm"
include "ciun.mm"
include "mpt2mpts.mm"
include "csbex.mm"
include "dfmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfop.mm"
include "nfsn.mm"
include "nfcsb.mm"
include "wceq.mm"
include "id.mm"
include "csbopeq1a.mm"
include "opeq12d.mm"
include "sneqd.mm"
include "iunxpf.mm"
include "3eqtri.mm"

theorem dfmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  assume dfmpt2.1: |- C e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint B w
  disjoint C w
  assert |- ( x e. A , y e. B |-> C ) = U_ x e. A U_ y e. B { <. <. x , y >. , C >. }

  proof
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vw
    cA
    cB
    cxp
    #
    vx
    vw
    cv
    #
    c1st
    cfv
    #
    vy
    @1
    c2nd
    cfv
    #
    cC
    csb
    #
    csb
    #
    cmpt
    vw
    @0
    @1
    @5
    cop
    #
    csn
    #
    ciun
    vx
    cA
    vy
    cB
    vx
    cv
    vy
    cv
    cop
    #
    cC
    cop
    #
    csn
    #
    ciun
    ciun
    vx
    vy
    vw
    cA
    cB
    cC
    mpt2mpts
    vw
    @0
    @5
    vx
    @2
    @4
    vy
    @3
    cC
    dfmpt2.1
    csbex
    csbex
    dfmpt
    vw
    vx
    vy
    cA
    cB
    @7
    @10
    vx
    @6
    vx
    @1
    @5
    vx
    @1
    nfcv
    vx
    @2
    @4
    nfcsb1v
    nfop
    nfsn
    vy
    @6
    vy
    @1
    @5
    vy
    @1
    nfcv
    vy
    vx
    @2
    @4
    vy
    @2
    nfcv
    vy
    @3
    cC
    nfcsb1v
    nfcsb
    nfop
    nfsn
    vw
    @10
    nfcv
    @1
    @8
    wceq
    #
    @6
    @9
    @11
    @1
    @8
    @5
    cC
    @11
    id
    vx
    vy
    @1
    cC
    csbopeq1a
    opeq12d
    sneqd
    iunxpf
    3eqtri
end
