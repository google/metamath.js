include "crg.mm"
include "wcel.mm"
include "cnzr.mm"
include "ply1nz.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "simpl.mm"
include "eqid.mm"
include "nzrnz.mm"
include "adantl.mm"
include "wceq.mm"
include "cv.mm"
include "c1o.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "wral.mm"
include "ifeq1.mm"
include "ifid.mm"
include "syl6eq.mm"
include "ralrimivw.mm"
include "cmpt.mm"
include "cmpl.mm"
include "con0.mm"
include "ply1mpl1.mm"
include "1on.mm"
include "a1i.mm"
include "mpl1.mm"
include "ply1mpl0.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "mpl0.mm"
include "fconstmpt.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "ifex.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "syl5ibr.mm"
include "necon3d.mm"
include "mpd.mm"
include "isnzr.mm"
include "sylanbrc.mm"
include "ex.mm"
include "impbid2.mm"

theorem ply1nzb
  let cP: class P
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume ply1domn.p: |- P = ( Poly1 ` R )


  assert |- ( R e. Ring -> ( R e. NzRing <-> P e. NzRing ) )

  proof
    cR
    crg
    wcel
    #
    cR
    cnzr
    wcel
    #
    cP
    cnzr
    wcel
    #
    cP
    cR
    ply1domn.p
    ply1nz
    @0
    @2
    @1
    @0
    @2
    wa
    #
    @0
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
    @1
    @0
    @2
    simpl
    #
    @3
    cP
    cur
    cfv
    #
    cP
    c0g
    cfv
    #
    wne
    #
    @6
    @2
    @10
    @0
    cP
    @8
    @9
    @8
    eqid
    #
    @9
    eqid
    #
    nzrnz
    adantl
    @3
    @4
    @5
    @8
    @9
    @4
    @5
    wceq
    #
    @8
    @9
    wceq
    #
    @3
    vy
    cv
    c1o
    cc0
    csn
    cxp
    wceq
    #
    @4
    @5
    cif
    #
    @5
    wceq
    #
    vy
    vx
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vx
    cn0
    c1o
    cmap
    co
    crab
    #
    wral
    #
    @13
    @17
    vy
    @18
    @13
    @16
    @15
    @5
    @5
    cif
    @5
    @15
    @4
    @5
    @5
    ifeq1
    @15
    @5
    ifid
    syl6eq
    ralrimivw
    @3
    @14
    vy
    @18
    @16
    cmpt
    #
    vy
    @18
    @5
    cmpt
    #
    wceq
    #
    @19
    @3
    @8
    @20
    @9
    @21
    @3
    vy
    @18
    c1o
    cR
    cmpl
    co
    #
    cR
    @8
    @4
    vx
    c1o
    con0
    @5
    @23
    eqid
    #
    @18
    eqid
    #
    @5
    eqid
    #
    @4
    eqid
    #
    cP
    cR
    @8
    @23
    @24
    ply1domn.p
    @11
    ply1mpl1
    c1o
    con0
    wcel
    @3
    1on
    a1i
    #
    @7
    mpl1
    @3
    @9
    @18
    @5
    csn
    cxp
    @21
    @3
    @18
    @23
    cR
    vx
    c1o
    @5
    con0
    @9
    @24
    @25
    @26
    cP
    cR
    @23
    @9
    @24
    ply1domn.p
    @12
    ply1mpl0
    @28
    @3
    @0
    cR
    cgrp
    wcel
    @7
    cR
    ringgrp
    syl
    mpl0
    vy
    @18
    @5
    fconstmpt
    syl6eq
    eqeq12d
    @16
    cvv
    wcel
    #
    vy
    @18
    wral
    @22
    @19
    wb
    @29
    vy
    @18
    @15
    @4
    @5
    cR
    cur
    fvex
    cR
    c0g
    fvex
    ifex
    rgenw
    vy
    @18
    @16
    @5
    cvv
    mpteqb
    ax-mp
    syl6bb
    syl5ibr
    necon3d
    mpd
    cR
    @4
    @5
    @27
    @26
    isnzr
    sylanbrc
    ex
    impbid2
end
