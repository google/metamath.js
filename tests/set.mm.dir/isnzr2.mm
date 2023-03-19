include "cnzr.mm"
include "wcel.mm"
include "crg.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "wa.mm"
include "c2o.mm"
include "cdom.mm"
include "wbr.mm"
include "eqid.mm"
include "isnzr.mm"
include "c1o.mm"
include "csdm.mm"
include "cv.mm"
include "wceq.mm"
include "wn.mm"
include "wrex.mm"
include "ringidcl.mm"
include "adantr.mm"
include "ring0cl.mm"
include "simpr.mm"
include "df-ne.mm"
include "neeq1.mm"
include "syl5bbr.mm"
include "neeq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "ex.mm"
include "wi.mm"
include "ring1eq0.mm"
include "3expb.mm"
include "necon3bd.mm"
include "rexlimdvva.mm"
include "impbid.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "1sdom.mm"
include "ax-mp.mm"
include "syl6bbr.mm"
include "csuc.mm"
include "com.mm"
include "1onn.mm"
include "sucdom.mm"
include "df-2o.mm"
include "breq1i.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isnzr2
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume isnzr2.b: |- B = ( Base ` R )


  assert |- ( R e. NzRing <-> ( R e. Ring /\ 2o ~<_ B ) )

  proof
    cR
    cnzr
    wcel
    cR
    crg
    wcel
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    wne
    #
    wa
    #
    @0
    c2o
    cB
    cdom
    wbr
    #
    wa
    cR
    @1
    @2
    @1
    eqid
    #
    @2
    eqid
    #
    isnzr
    @0
    @3
    @5
    @0
    @3
    c1o
    cB
    csdm
    wbr
    #
    @5
    @0
    @3
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    wn
    #
    vy
    cB
    wrex
    vx
    cB
    wrex
    #
    @8
    @0
    @3
    @13
    @0
    @3
    @13
    @4
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    @3
    @13
    @0
    @14
    @3
    cB
    cR
    @1
    isnzr2.b
    @6
    ringidcl
    adantr
    @0
    @15
    @3
    cB
    cR
    @2
    isnzr2.b
    @7
    ring0cl
    adantr
    @0
    @3
    simpr
    @12
    @3
    @1
    @10
    wne
    #
    vx
    vy
    @1
    @2
    cB
    cB
    @12
    @9
    @10
    wne
    @9
    @1
    wceq
    @16
    @9
    @10
    df-ne
    @9
    @1
    @10
    neeq1
    syl5bbr
    @10
    @2
    @1
    neeq2
    rspc2ev
    syl3anc
    ex
    @0
    @12
    @3
    vx
    vy
    cB
    cB
    @0
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    wa
    wa
    @11
    @1
    @2
    @0
    @17
    @18
    @1
    @2
    wceq
    @11
    wi
    cB
    cR
    @1
    @9
    @10
    @2
    isnzr2.b
    @6
    @7
    ring1eq0
    3expb
    necon3bd
    rexlimdvva
    impbid
    cB
    cvv
    wcel
    @8
    @13
    wb
    cB
    cR
    cbs
    cfv
    cvv
    isnzr2.b
    cR
    cbs
    fvex
    eqeltri
    vx
    vy
    cB
    cvv
    1sdom
    ax-mp
    syl6bbr
    @8
    c1o
    csuc
    #
    cB
    cdom
    wbr
    #
    @5
    c1o
    com
    wcel
    @8
    @20
    wb
    1onn
    c1o
    cB
    sucdom
    ax-mp
    c2o
    @19
    cB
    cdom
    df-2o
    breq1i
    bitr4i
    syl6bb
    pm5.32i
    bitri
end
