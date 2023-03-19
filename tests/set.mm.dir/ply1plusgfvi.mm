include "cid.mm"
include "cfv.mm"
include "cpl1.mm"
include "cplusg.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvi.mm"
include "fveq2d.mm"
include "wn.mm"
include "c0.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cof.mm"
include "cres.mm"
include "eqid.mm"
include "ply1plusg.mm"
include "cmps.mm"
include "cxp.mm"
include "mplplusg.mm"
include "cbs.mm"
include "cn0.mm"
include "cmap.mm"
include "wtru.mm"
include "con0.mm"
include "base0.mm"
include "psr1baslem.mm"
include "1on.mm"
include "a1i.mm"
include "psrbas.mm"
include "trud.mm"
include "cc0.mm"
include "csn.mm"
include "wne.mm"
include "wf.mm"
include "0nn0.mm"
include "fconst6.mm"
include "nn0ex.mm"
include "elexi.mm"
include "elmap.mm"
include "mpbir.mm"
include "ne0i.mm"
include "map0b.mm"
include "mp2b.mm"
include "eqtr2i.mm"
include "psrplusg.mm"
include "xp0.mm"
include "reseq2i.mm"
include "3eqtri.mm"
include "res0.mm"
include "c2.mm"
include "df-plusg.mm"
include "str0.mm"
include "eqtri.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqcomi.mm"

theorem ply1plusgfvi
  let cR: class R
  let va: setvar a


  assert |- ( +g ` ( Poly1 ` R ) ) = ( +g ` ( Poly1 ` ( _I ` R ) ) )

  proof
    cR
    cid
    cfv
    #
    cpl1
    cfv
    #
    cplusg
    cfv
    #
    cR
    cpl1
    cfv
    #
    cplusg
    cfv
    #
    cR
    cvv
    wcel
    #
    @2
    @4
    wceq
    @5
    @1
    @3
    cplusg
    @5
    @0
    cR
    cpl1
    cR
    cvv
    fvi
    fveq2d
    fveq2d
    @5
    wn
    #
    c0
    cpl1
    cfv
    #
    cplusg
    cfv
    #
    c0
    cplusg
    cfv
    #
    @2
    @4
    @8
    c1o
    c0
    cmpl
    co
    #
    cplusg
    cfv
    #
    @9
    cof
    #
    c0
    cres
    #
    @9
    @8
    c0
    @10
    @7
    @7
    eqid
    @10
    eqid
    #
    @8
    eqid
    ply1plusg
    @11
    c1o
    c0
    cmps
    co
    #
    cplusg
    cfv
    #
    @12
    c0
    c0
    cxp
    #
    cres
    @13
    @11
    c0
    @15
    c1o
    @10
    @14
    @15
    eqid
    #
    @11
    eqid
    mplplusg
    c0
    @9
    @16
    c0
    @15
    c1o
    @18
    @15
    cbs
    cfv
    #
    c0
    cn0
    c1o
    cmap
    co
    #
    cmap
    co
    #
    c0
    @19
    @21
    wceq
    wtru
    @19
    @20
    c0
    @15
    va
    c1o
    c0
    con0
    @18
    base0
    va
    psr1baslem
    @19
    eqid
    c1o
    con0
    wcel
    wtru
    1on
    a1i
    psrbas
    trud
    c1o
    cc0
    csn
    cxp
    #
    @20
    wcel
    #
    @20
    c0
    wne
    @21
    c0
    wceq
    @23
    c1o
    cn0
    @22
    wf
    c1o
    cc0
    cn0
    0nn0
    fconst6
    cn0
    c1o
    @22
    nn0ex
    c1o
    con0
    1on
    elexi
    elmap
    mpbir
    @20
    @22
    ne0i
    @20
    map0b
    mp2b
    eqtr2i
    @9
    eqid
    @16
    eqid
    psrplusg
    @17
    c0
    @12
    c0
    xp0
    reseq2i
    3eqtri
    @13
    c0
    @9
    @12
    res0
    cplusg
    c2
    df-plusg
    str0
    eqtri
    3eqtri
    @6
    @1
    @7
    cplusg
    @6
    @0
    c0
    cpl1
    cR
    cid
    fvprc
    fveq2d
    fveq2d
    @6
    @3
    c0
    cplusg
    cR
    cpl1
    fvprc
    fveq2d
    3eqtr4a
    pm2.61i
    eqcomi
end
