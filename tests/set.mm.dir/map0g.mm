include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "fconst6g.mm"
include "elmapg.mm"
include "syl5ibr.mm"
include "ne0i.mm"
include "syl6.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "necon4d.mm"
include "f0.mm"
include "feq2.mm"
include "mpbiri.mm"
include "necon2d.mm"
include "jcad.mm"
include "oveq1.mm"
include "map0b.mm"
include "sylan9eq.mm"
include "impbid1.mm"

theorem map0g
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vf: setvar f


  assert |- ( ( A e. V /\ B e. W ) -> ( ( A ^m B ) = (/) <-> ( A = (/) /\ B =/= (/) ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cB
    cmap
    co
    #
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    cB
    c0
    wne
    #
    wa
    @0
    @2
    @3
    @4
    @0
    cA
    c0
    @1
    c0
    cA
    c0
    wne
    vf
    cv
    #
    cA
    wcel
    #
    vf
    wex
    @0
    @1
    c0
    wne
    #
    vf
    cA
    n0
    @0
    @6
    @7
    vf
    @0
    @6
    cB
    @5
    csn
    cxp
    #
    @1
    wcel
    #
    @7
    @6
    @9
    @0
    cB
    cA
    @8
    wf
    cB
    @5
    cA
    fconst6g
    cA
    cB
    @8
    cV
    cW
    elmapg
    syl5ibr
    @1
    @8
    ne0i
    syl6
    exlimdv
    syl5bi
    necon4d
    @0
    cB
    c0
    @1
    c0
    @0
    cB
    c0
    wceq
    #
    c0
    @1
    wcel
    #
    @7
    @10
    @11
    @0
    cB
    cA
    c0
    wf
    #
    @10
    @12
    c0
    cA
    c0
    wf
    cA
    f0
    cB
    c0
    cA
    c0
    feq2
    mpbiri
    cA
    cB
    c0
    cV
    cW
    elmapg
    syl5ibr
    @1
    c0
    ne0i
    syl6
    necon2d
    jcad
    @3
    @4
    @1
    c0
    cB
    cmap
    co
    c0
    cA
    c0
    cB
    cmap
    oveq1
    cB
    map0b
    sylan9eq
    impbid1
end
