include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "breq2.mm"
include "mpbiri.mm"
include "adantl.mm"
include "cneg.mm"
include "simplr.mm"
include "simpr.mm"
include "breqtrd.mm"
include "wn.mm"
include "cn0.mm"
include "1nn0.mm"
include "nn0nlt0.mm"
include "ax-mp.mm"
include "wb.mm"
include "1re.mm"
include "lt0neg1.mm"
include "mtbi.mm"
include "a1i.mm"
include "pm2.21dd.mm"
include "gt0ne0d.mm"
include "pm2.21ddne.mm"
include "cxr.mm"
include "ctp.mm"
include "w3o.mm"
include "remulcl.mm"
include "rexrd.mm"
include "adantr.mm"
include "sgncl.mm"
include "eltpi.mm"
include "3syl.mm"
include "mpjao3dan.mm"
include "impbida.mm"
include "sgnpbi.mm"
include "syl.mm"
include "sgnmul.mm"
include "breq2d.mm"
include "3bitr3d.mm"

theorem sgnmulsgp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 < ( A x. B ) <-> 0 < ( ( sgn ` A ) x. ( sgn ` B ) ) ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cA
    cB
    cmul
    co
    #
    csgn
    cfv
    #
    c1
    wceq
    #
    cc0
    @2
    clt
    wbr
    #
    cc0
    @1
    clt
    wbr
    #
    cc0
    cA
    csgn
    cfv
    cB
    csgn
    cfv
    cmul
    co
    #
    clt
    wbr
    @0
    @3
    @4
    @3
    @4
    @0
    @3
    @4
    cc0
    c1
    clt
    wbr
    0lt1
    @2
    c1
    cc0
    clt
    breq2
    mpbiri
    adantl
    @0
    @4
    wa
    #
    @2
    c1
    cneg
    #
    wceq
    #
    @3
    @2
    cc0
    wceq
    #
    @3
    @7
    @9
    wa
    #
    cc0
    @8
    clt
    wbr
    #
    @3
    @11
    cc0
    @2
    @8
    clt
    @0
    @4
    @9
    simplr
    @7
    @9
    simpr
    breqtrd
    @12
    wn
    @11
    c1
    cc0
    clt
    wbr
    #
    @12
    c1
    cn0
    wcel
    @13
    wn
    1nn0
    c1
    nn0nlt0
    ax-mp
    c1
    cr
    wcel
    @13
    @12
    wb
    1re
    c1
    lt0neg1
    ax-mp
    mtbi
    a1i
    pm2.21dd
    @7
    @10
    wa
    #
    @3
    @2
    cc0
    @7
    @10
    simpr
    @14
    @2
    @0
    @4
    @10
    simplr
    gt0ne0d
    pm2.21ddne
    @7
    @3
    simpr
    @7
    @1
    cxr
    wcel
    #
    @2
    @8
    cc0
    c1
    ctp
    wcel
    @9
    @10
    @3
    w3o
    @0
    @15
    @4
    @0
    @1
    cA
    cB
    remulcl
    rexrd
    #
    adantr
    @1
    sgncl
    @2
    @8
    cc0
    c1
    eltpi
    3syl
    mpjao3dan
    impbida
    @0
    @15
    @3
    @5
    wb
    @16
    @1
    sgnpbi
    syl
    @0
    @2
    @6
    cc0
    clt
    cA
    cB
    sgnmul
    breq2d
    3bitr3d
end
