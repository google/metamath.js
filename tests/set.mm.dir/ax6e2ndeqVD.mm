include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wex.mm"
include "ax6e2nd.mm"
include "wi.mm"
include "ax6e2eq.mm"
include "a1d.mm"
include "exmid.mm"
include "jao.mm"
include "e000.mm"
include "jaoi.mm"
include "wne.mm"
include "wb.mm"
include "idn1.mm"
include "idn2.mm"
include "simpl.mm"
include "e2.mm"
include "neeq1.mm"
include "biimprcd.mm"
include "e12.mm"
include "simpr.mm"
include "neeq2.mm"
include "e22.mm"
include "df-ne.mm"
include "bicomi.mm"
include "sp.mm"
include "con3i.mm"
include "sylbir.mm"
include "in2.mm"
include "gen11.mm"
include "exim.mm"
include "e1a.mm"
include "nfnae.mm"
include "19.9.mm"
include "imbi2.mm"
include "biimpcd.mm"
include "e10.mm"
include "excom.mm"
include "imbi1.mm"
include "hbnae.mm"
include "eximi.mm"
include "nfa1.mm"
include "sylib.mm"
include "syl.mm"
include "imim1.mm"
include "orc.mm"
include "imim2i.mm"
include "in1.mm"
include "ax-1.mm"
include "olc.mm"
include "exmidne.mm"
include "com12.mm"
include "impbii.mm"

theorem ax6e2ndeqVD
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( ( -. A. x x = y \/ u = v ) <-> E. x E. y ( x = u /\ y = v ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    vx
    wal
    #
    wn
    #
    vu
    cv
    #
    vv
    cv
    #
    wceq
    #
    wo
    #
    @0
    @5
    wceq
    #
    @1
    @6
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @4
    @12
    @7
    vx
    vy
    vv
    vu
    ax6e2nd
    #
    @3
    @7
    @12
    wi
    #
    wi
    @4
    @14
    wi
    @3
    @4
    wo
    @14
    vx
    vy
    vv
    vu
    ax6e2eq
    @4
    @12
    @7
    @13
    a1d
    @3
    exmid
    @3
    @14
    @4
    jao
    e000
    jaoi
    @5
    @6
    wne
    #
    @12
    @8
    wi
    #
    wi
    #
    @7
    @16
    wi
    #
    @7
    @15
    wo
    #
    @16
    @15
    @16
    @15
    @12
    @4
    wi
    #
    @16
    @15
    @12
    @4
    vy
    wex
    #
    wi
    #
    @21
    @4
    wi
    @20
    @15
    @11
    vx
    wex
    #
    vy
    wex
    #
    @21
    wi
    #
    @12
    @24
    wb
    #
    @22
    @15
    @23
    @4
    wi
    #
    vy
    wal
    @25
    @15
    @27
    vy
    @15
    @23
    @4
    vx
    wex
    #
    wi
    #
    @28
    @4
    wb
    #
    @27
    @15
    @11
    @4
    wi
    #
    vx
    wal
    @29
    @15
    @31
    vx
    @15
    @11
    @4
    @15
    @11
    @0
    @1
    wne
    #
    @4
    @15
    @11
    @0
    @6
    wne
    #
    @10
    @32
    @15
    @15
    @11
    @9
    @33
    @15
    idn1
    @15
    @11
    @11
    @9
    @15
    @11
    idn2
    #
    @9
    @10
    simpl
    e2
    @9
    @33
    @15
    @0
    @5
    @6
    neeq1
    biimprcd
    e12
    @15
    @11
    @11
    @10
    @34
    @9
    @10
    simpr
    e2
    @10
    @32
    @33
    @1
    @6
    @0
    neeq2
    biimprcd
    e22
    @32
    @2
    wn
    #
    @4
    @32
    @35
    @0
    @1
    df-ne
    bicomi
    @3
    @2
    @2
    vx
    sp
    con3i
    sylbir
    e2
    in2
    gen11
    @11
    @4
    vx
    exim
    e1a
    @4
    vx
    vx
    vy
    vx
    nfnae
    19.9
    @30
    @29
    @27
    @28
    @4
    @23
    imbi2
    biimpcd
    e10
    gen11
    @23
    @4
    vy
    exim
    e1a
    @11
    vx
    vy
    excom
    @26
    @22
    @25
    @12
    @24
    @21
    imbi1
    biimprcd
    e10
    @21
    @4
    vy
    wal
    #
    @4
    @21
    @36
    vy
    wex
    @36
    @4
    @36
    vy
    vx
    vy
    vy
    hbnae
    eximi
    @36
    vy
    @4
    vy
    nfa1
    19.9
    sylib
    @4
    vy
    sp
    syl
    @12
    @21
    @4
    imim1
    e10
    @4
    @8
    @12
    @4
    @7
    orc
    imim2i
    e1a
    in1
    @7
    @16
    @7
    @12
    @7
    wi
    #
    @16
    @7
    @7
    @37
    @7
    idn1
    @7
    @12
    ax-1
    e1a
    @7
    @8
    @12
    @7
    @4
    olc
    imim2i
    e1a
    in1
    @5
    @6
    exmidne
    @18
    @17
    @19
    @16
    wi
    @7
    @16
    @15
    jao
    com12
    e000
    impbii
end
