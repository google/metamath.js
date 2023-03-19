include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "wi.mm"
include "isfi.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "wa.mm"
include "cima.mm"
include "wfo.mm"
include "f1ofo.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "syl5sseq.mm"
include "syl.mm"
include "ssnnfi.mm"
include "sylib.mm"
include "sylan2.mm"
include "adantrr.mm"
include "cres.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1ores.mm"
include "sylan.mm"
include "vex.mm"
include "resex.mm"
include "f1oeq1.mm"
include "spcev.mm"
include "sylibr.mm"
include "entr.mm"
include "ex.mm"
include "reximdv.mm"
include "syl6ibr.mm"
include "adantl.mm"
include "mpd.mm"
include "exp32.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "imp.mm"

theorem ssfi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A e. Fin /\ B C_ A ) -> B e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    wss
    #
    cB
    cfn
    wcel
    #
    @0
    cA
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    @1
    @2
    wi
    #
    vx
    cA
    isfi
    @4
    @5
    vx
    com
    @4
    cA
    @3
    vz
    cv
    #
    wf1o
    #
    vz
    wex
    @3
    com
    wcel
    #
    @5
    cA
    @3
    vz
    bren
    @8
    @7
    @5
    vz
    @8
    @7
    @1
    @2
    @8
    @7
    @1
    wa
    #
    wa
    @6
    cB
    cima
    #
    vy
    cv
    #
    cen
    wbr
    #
    vy
    com
    wrex
    #
    @2
    @8
    @7
    @13
    @1
    @7
    @8
    @10
    @3
    wss
    #
    @13
    @7
    cA
    @3
    @6
    wfo
    #
    @14
    cA
    @3
    @6
    f1ofo
    @15
    @6
    crn
    @10
    @3
    @6
    cB
    imassrn
    cA
    @3
    @6
    forn
    syl5sseq
    syl
    @8
    @14
    wa
    @10
    cfn
    wcel
    @13
    @3
    @10
    ssnnfi
    vy
    @10
    isfi
    sylib
    sylan2
    adantrr
    @9
    @13
    @2
    wi
    @8
    @9
    @13
    cB
    @11
    cen
    wbr
    #
    vy
    com
    wrex
    @2
    @9
    @12
    @16
    vy
    com
    @9
    @12
    @16
    @9
    cB
    @10
    @6
    cB
    cres
    #
    wf1o
    #
    @12
    @16
    @7
    cA
    @3
    @6
    wf1
    @1
    @18
    cA
    @3
    @6
    f1of1
    cA
    @3
    cB
    @6
    f1ores
    sylan
    @18
    cB
    @10
    cen
    wbr
    #
    @12
    @16
    @18
    cB
    @10
    @3
    wf1o
    #
    vx
    wex
    @19
    @20
    @18
    vx
    @17
    @6
    cB
    vz
    vex
    resex
    cB
    @10
    @3
    @17
    f1oeq1
    spcev
    cB
    @10
    vx
    bren
    sylibr
    cB
    @10
    @11
    entr
    sylan
    sylan
    ex
    reximdv
    vy
    cB
    isfi
    syl6ibr
    adantl
    mpd
    exp32
    exlimdv
    syl5bi
    rexlimiv
    sylbi
    imp
end
