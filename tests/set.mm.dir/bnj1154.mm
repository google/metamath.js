include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "w-bnj17.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "bnj658.mm"
include "wi.mm"
include "wceq.mm"
include "wex.mm"
include "elisset.mm"
include "bnj708.mm"
include "wa.mm"
include "wal.mm"
include "df-fr.mm"
include "biimpi.mm"
include "19.21bi.mm"
include "3impib.mm"
include "sseq1.mm"
include "neeq1.mm"
include "3anbi23d.mm"
include "raleq.mm"
include "rexeqbi1dv.mm"
include "imbi12d.mm"
include "mpbii.mm"
include "bnj593.mm"
include "bnj937.mm"
include "mpd.mm"

theorem bnj1154
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint A b
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint R b
  assert |- ( ( R Fr A /\ B C_ A /\ B =/= (/) /\ B e. _V ) -> E. x e. B A. y e. B -. y R x )

  proof
    cA
    cR
    wfr
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    cB
    cvv
    wcel
    #
    w-bnj17
    #
    @0
    @1
    @2
    w3a
    #
    vy
    cv
    vx
    cv
    cR
    wbr
    wn
    #
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    @0
    @1
    @2
    @3
    bnj658
    @4
    @5
    @8
    wi
    #
    vb
    @4
    vb
    cv
    #
    cB
    wceq
    #
    @9
    vb
    @0
    @1
    @2
    @3
    @11
    vb
    wex
    vb
    cB
    cvv
    elisset
    bnj708
    @11
    @0
    @10
    cA
    wss
    #
    @10
    c0
    wne
    #
    w3a
    #
    @6
    vy
    @10
    wral
    #
    vx
    @10
    wrex
    #
    wi
    @9
    @0
    @12
    @13
    @16
    @0
    @12
    @13
    wa
    @16
    wi
    #
    vb
    @0
    @17
    vb
    wal
    vb
    vx
    vy
    cA
    cR
    df-fr
    biimpi
    19.21bi
    3impib
    @11
    @14
    @5
    @16
    @8
    @11
    @12
    @1
    @13
    @2
    @0
    @10
    cB
    cA
    sseq1
    @10
    cB
    c0
    neeq1
    3anbi23d
    @15
    @7
    vx
    @10
    cB
    @6
    vy
    @10
    cB
    raleq
    rexeqbi1dv
    imbi12d
    mpbii
    bnj593
    bnj937
    mpd
end
