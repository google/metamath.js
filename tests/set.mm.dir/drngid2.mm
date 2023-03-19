include "cdr.mm"
include "wcel.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cmgp.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "c0g.mm"
include "wa.mm"
include "df-3an.mm"
include "eldifsn.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "cgrp.mm"
include "wb.mm"
include "eqid.mm"
include "drngmgp.mm"
include "wss.mm"
include "cbs.mm"
include "difss.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "mp2b.mm"
include "isgrpid2.mm"
include "syl.mm"
include "syl5bb.mm"
include "drngid.mm"
include "eqeq1d.mm"
include "bitr4d.mm"

theorem drngid2
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cI: class I
  let c.0: class .0.
  assume drngid2.b: |- B = ( Base ` R )
  assume drngid2.t: |- .x. = ( .r ` R )
  assume drngid2.o: |- .0. = ( 0g ` R )
  assume drngid2.u: |- .1. = ( 1r ` R )


  assert |- ( R e. DivRing -> ( ( I e. B /\ I =/= .0. /\ ( I .x. I ) = I ) <-> .1. = I ) )

  proof
    cR
    cdr
    wcel
    #
    cI
    cB
    wcel
    #
    cI
    c.0
    wne
    #
    cI
    cI
    c.x
    co
    cI
    wceq
    #
    w3a
    #
    cR
    cmgp
    cfv
    #
    cB
    c.0
    csn
    #
    cdif
    #
    cress
    co
    #
    c0g
    cfv
    #
    cI
    wceq
    #
    c.1
    cI
    wceq
    @4
    cI
    @7
    wcel
    #
    @3
    wa
    #
    @0
    @10
    @4
    @1
    @2
    wa
    #
    @3
    wa
    @12
    @1
    @2
    @3
    df-3an
    @11
    @13
    @3
    cI
    cB
    c.0
    eldifsn
    anbi1i
    bitr4i
    @0
    @8
    cgrp
    wcel
    @12
    @10
    wb
    cB
    cR
    @8
    c.0
    drngid2.b
    drngid2.o
    @8
    eqid
    #
    drngmgp
    @7
    c.x
    @8
    @9
    cI
    @7
    cB
    wss
    @7
    @8
    cbs
    cfv
    wceq
    cB
    @6
    difss
    @7
    cB
    @8
    @5
    @14
    cB
    cR
    @5
    @5
    eqid
    #
    drngid2.b
    mgpbas
    ressbas2
    ax-mp
    cB
    cvv
    wcel
    @7
    cvv
    wcel
    c.x
    @8
    cplusg
    cfv
    wceq
    cB
    cR
    cbs
    cfv
    cvv
    drngid2.b
    cR
    cbs
    fvex
    eqeltri
    cB
    @6
    cvv
    difexg
    @7
    c.x
    @5
    @8
    cvv
    @14
    cR
    c.x
    @5
    @15
    drngid2.t
    mgpplusg
    ressplusg
    mp2b
    @9
    eqid
    isgrpid2
    syl
    syl5bb
    @0
    c.1
    @9
    cI
    cB
    cR
    c.1
    @8
    c.0
    drngid2.b
    drngid2.o
    drngid2.u
    @14
    drngid
    eqeq1d
    bitr4d
end
