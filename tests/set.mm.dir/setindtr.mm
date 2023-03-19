include "cv.mm"
include "wtr.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "cin.mm"
include "wrex.mm"
include "wn.mm"
include "wral.mm"
include "nfv.mm"
include "nfa1.mm"
include "nfan.mm"
include "eldifn.mm"
include "adantl.mm"
include "trss.mm"
include "eldifi.mm"
include "impel.mm"
include "df-ss.mm"
include "sylib.mm"
include "adantlr.mm"
include "sseq1d.mm"
include "sp.mm"
include "ad2antlr.mm"
include "sylbid.mm"
include "mtod.mm"
include "inssdif0.mm"
include "sylnib.mm"
include "ex.mm"
include "ralrimi.mm"
include "ralnex.mm"
include "cvv.mm"
include "wne.mm"
include "vex.mm"
include "difexi.mm"
include "zfreg.mm"
include "mpan.mm"
include "necon1bi.mm"
include "syl.mm"
include "ssdif0.mm"
include "sylibr.mm"
include "simplr.mm"
include "sseldd.mm"
include "exlimiv.mm"
include "com12.mm"

theorem setindtr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( A. x ( x C_ A -> x e. A ) -> ( E. y ( Tr y /\ B e. y ) -> B e. A ) )

  proof
    vy
    cv
    #
    wtr
    #
    cB
    @0
    wcel
    #
    wa
    #
    vy
    wex
    vx
    cv
    #
    cA
    wss
    #
    @4
    cA
    wcel
    #
    wi
    #
    vx
    wal
    #
    cB
    cA
    wcel
    #
    @3
    @8
    @9
    wi
    vy
    @3
    @8
    @9
    @3
    @8
    wa
    @0
    cA
    cB
    @1
    @8
    @0
    cA
    wss
    #
    @2
    @1
    @8
    wa
    #
    @0
    cA
    cdif
    #
    c0
    wceq
    #
    @10
    @11
    @4
    @12
    cin
    c0
    wceq
    #
    vx
    @12
    wrex
    #
    wn
    #
    @13
    @11
    @14
    wn
    #
    vx
    @12
    wral
    @16
    @11
    @17
    vx
    @12
    @1
    @8
    vx
    @1
    vx
    nfv
    @7
    vx
    nfa1
    nfan
    @11
    @4
    @12
    wcel
    #
    @17
    @11
    @18
    wa
    #
    @4
    @0
    cin
    #
    cA
    wss
    #
    @14
    @19
    @21
    @6
    @18
    @6
    wn
    @11
    @4
    @0
    cA
    eldifn
    adantl
    @19
    @21
    @5
    @6
    @19
    @20
    @4
    cA
    @1
    @18
    @20
    @4
    wceq
    #
    @8
    @1
    @18
    wa
    @4
    @0
    wss
    #
    @22
    @1
    @4
    @0
    wcel
    @23
    @18
    @0
    @4
    trss
    @4
    @0
    cA
    eldifi
    impel
    @4
    @0
    df-ss
    sylib
    adantlr
    sseq1d
    @8
    @7
    @1
    @18
    @7
    vx
    sp
    ad2antlr
    sylbid
    mtod
    @4
    @0
    cA
    inssdif0
    sylnib
    ex
    ralrimi
    @14
    vx
    @12
    ralnex
    sylib
    @15
    @12
    c0
    @12
    cvv
    wcel
    @12
    c0
    wne
    @15
    @0
    cA
    vy
    vex
    difexi
    vx
    @12
    cvv
    zfreg
    mpan
    necon1bi
    syl
    @0
    cA
    ssdif0
    sylibr
    adantlr
    @1
    @2
    @8
    simplr
    sseldd
    ex
    exlimiv
    com12
end
