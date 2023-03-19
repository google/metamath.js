include "csm.mm"
include "co.mm"
include "csp.mm"
include "csqrt.mm"
include "cfv.mm"
include "ccj.mm"
include "cmul.mm"
include "cno.mm"
include "cabs.mm"
include "his35i.mm"
include "fveq2i.mm"
include "cjmulrcli.mm"
include "chil.mm"
include "wcel.mm"
include "cr.mm"
include "hiidrcl.mm"
include "ax-mp.mm"
include "cjmulge0i.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "hiidge0.mm"
include "sqrtmulii.mm"
include "eqtri.mm"
include "wceq.mm"
include "hvmulcli.mm"
include "normval.mm"
include "cc.mm"
include "absval.mm"
include "oveq12i.mm"
include "3eqtr4i.mm"

theorem norm-iii-i
  let cA: class A
  let cB: class B
  assume norm-iii.1: |- A e. CC
  assume norm-iii.2: |- B e. ~H


  assert |- ( normh ` ( A .h B ) ) = ( ( abs ` A ) x. ( normh ` B ) )

  proof
    cA
    cB
    csm
    co
    #
    @0
    csp
    co
    #
    csqrt
    cfv
    #
    cA
    cA
    ccj
    cfv
    cmul
    co
    #
    csqrt
    cfv
    #
    cB
    cB
    csp
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    @0
    cno
    cfv
    #
    cA
    cabs
    cfv
    #
    cB
    cno
    cfv
    #
    cmul
    co
    @2
    @3
    @5
    cmul
    co
    #
    csqrt
    cfv
    @7
    @1
    @11
    csqrt
    cA
    cA
    cB
    cB
    norm-iii.1
    norm-iii.1
    norm-iii.2
    norm-iii.2
    his35i
    fveq2i
    @3
    @5
    cA
    norm-iii.1
    cjmulrcli
    cB
    chil
    wcel
    #
    @5
    cr
    wcel
    norm-iii.2
    cB
    hiidrcl
    ax-mp
    cA
    norm-iii.1
    cjmulge0i
    @12
    cc0
    @5
    cle
    wbr
    norm-iii.2
    cB
    hiidge0
    ax-mp
    sqrtmulii
    eqtri
    @0
    chil
    wcel
    @8
    @2
    wceq
    cA
    cB
    norm-iii.1
    norm-iii.2
    hvmulcli
    @0
    normval
    ax-mp
    @9
    @4
    @10
    @6
    cmul
    cA
    cc
    wcel
    @9
    @4
    wceq
    norm-iii.1
    cA
    absval
    ax-mp
    @12
    @10
    @6
    wceq
    norm-iii.2
    cB
    normval
    ax-mp
    oveq12i
    3eqtr4i
end
