include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "wceq.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "neg1lt0.mm"
include "breq1.mm"
include "mpbiri.mm"
include "adantl.mm"
include "simpr.mm"
include "simplr.mm"
include "lt0ne0d.mm"
include "pm2.21ddne.mm"
include "eqbrtrrd.mm"
include "cn0.mm"
include "wn.mm"
include "1nn0.mm"
include "nn0nlt0.mm"
include "mp1i.mm"
include "pm2.21dd.mm"
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
include "wb.mm"
include "sgnnbi.mm"
include "syl.mm"
include "sgnmul.mm"
include "breq1d.mm"
include "3bitr3d.mm"

theorem sgnmulsgn
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( A x. B ) < 0 <-> ( ( sgn ` A ) x. ( sgn ` B ) ) < 0 ) )

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
    cneg
    #
    wceq
    #
    @2
    cc0
    clt
    wbr
    #
    @1
    cc0
    clt
    wbr
    #
    cA
    csgn
    cfv
    cB
    csgn
    cfv
    cmul
    co
    #
    cc0
    clt
    wbr
    @0
    @4
    @5
    @4
    @5
    @0
    @4
    @5
    @3
    cc0
    clt
    wbr
    neg1lt0
    @2
    @3
    cc0
    clt
    breq1
    mpbiri
    adantl
    @0
    @5
    wa
    #
    @4
    @4
    @2
    cc0
    wceq
    #
    @2
    c1
    wceq
    #
    @8
    @4
    simpr
    @8
    @9
    wa
    #
    @4
    @2
    cc0
    @8
    @9
    simpr
    @11
    @2
    @0
    @5
    @9
    simplr
    lt0ne0d
    pm2.21ddne
    @8
    @10
    wa
    #
    c1
    cc0
    clt
    wbr
    #
    @4
    @12
    @2
    c1
    cc0
    clt
    @8
    @10
    simpr
    @0
    @5
    @10
    simplr
    eqbrtrrd
    c1
    cn0
    wcel
    @13
    wn
    @12
    1nn0
    c1
    nn0nlt0
    mp1i
    pm2.21dd
    @8
    @1
    cxr
    wcel
    #
    @2
    @3
    cc0
    c1
    ctp
    wcel
    @4
    @9
    @10
    w3o
    @0
    @14
    @5
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
    @3
    cc0
    c1
    eltpi
    3syl
    mpjao3dan
    impbida
    @0
    @14
    @4
    @6
    wb
    @15
    @1
    sgnnbi
    syl
    @0
    @2
    @7
    cc0
    clt
    cA
    cB
    sgnmul
    breq1d
    3bitr3d
end
