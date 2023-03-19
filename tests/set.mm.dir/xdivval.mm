include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "cxdiv.mm"
include "co.mm"
include "cv.mm"
include "cxmu.mm"
include "wceq.mm"
include "crio.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "simpl.mm"
include "eqeq2d.mm"
include "riotabidva.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "df-xdiv.mm"
include "riotaex.mm"
include "ovmpt2.mm"
include "sylan2br.mm"
include "3impb.mm"

theorem xdivval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( A e. RR* /\ B e. RR /\ B =/= 0 ) -> ( A /e B ) = ( iota_ x e. RR* ( B *e x ) = A ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    cA
    cB
    cxdiv
    co
    cB
    vx
    cv
    #
    cxmu
    co
    #
    cA
    wceq
    #
    vx
    cxr
    crio
    #
    wceq
    #
    @1
    @2
    wa
    @0
    cB
    cr
    cc0
    csn
    cdif
    #
    wcel
    @7
    cB
    cr
    cc0
    eldifsn
    vy
    vz
    cA
    cB
    cxr
    @8
    vz
    cv
    #
    @3
    cxmu
    co
    #
    vy
    cv
    #
    wceq
    #
    vx
    cxr
    crio
    @6
    cxdiv
    @10
    cA
    wceq
    #
    vx
    cxr
    crio
    @11
    cA
    wceq
    #
    @12
    @13
    vx
    cxr
    @14
    @3
    cxr
    wcel
    #
    wa
    @11
    cA
    @10
    @14
    @15
    simpl
    eqeq2d
    riotabidva
    @9
    cB
    wceq
    #
    @13
    @5
    vx
    cxr
    @16
    @15
    wa
    #
    @10
    @4
    cA
    @17
    @9
    cB
    @3
    cxmu
    @16
    @15
    simpl
    oveq1d
    eqeq1d
    riotabidva
    vy
    vz
    vx
    df-xdiv
    @5
    vx
    cxr
    riotaex
    ovmpt2
    sylan2br
    3impb
end
