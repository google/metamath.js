include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "eqidd.mm"
include "cvv.mm"
include "wceq.mm"
include "c0.mm"
include "c0g.mm"
include "wn.mm"
include "eqid.mm"
include "mndidcl.mm"
include "n0i.mm"
include "syl.mm"
include "cress.mm"
include "co.mm"
include "reldmress.mm"
include "ovprc2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "base0.mm"
include "syl6eqr.mm"
include "nsyl2.mm"
include "adantl.mm"
include "ressplusg.mm"
include "simpr.mm"
include "cv.mm"
include "simpl.mm"
include "ressbasss.mm"
include "sseli.mm"
include "cmncom.mm"
include "syl3an.mm"
include "iscmnd.mm"

theorem subcmn
  let cS: class S
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subgabl.h: |- H = ( G |`s S )


  assert |- ( ( G e. CMnd /\ H e. Mnd ) -> H e. CMnd )

  proof
    cG
    ccmn
    wcel
    #
    cH
    cmnd
    wcel
    #
    wa
    #
    vx
    vy
    cH
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    cH
    @2
    @3
    eqidd
    @2
    cS
    cvv
    wcel
    #
    @4
    cH
    cplusg
    cfv
    wceq
    @1
    @5
    @0
    @1
    @3
    c0
    wceq
    #
    @5
    @1
    cH
    c0g
    cfv
    #
    @3
    wcel
    @6
    wn
    @3
    cH
    @7
    @3
    eqid
    @7
    eqid
    mndidcl
    @3
    @7
    n0i
    syl
    @5
    wn
    #
    @3
    c0
    cbs
    cfv
    c0
    @8
    cH
    c0
    cbs
    @8
    cH
    cG
    cS
    cress
    co
    c0
    subgabl.h
    cG
    cS
    cress
    reldmress
    ovprc2
    syl5eq
    fveq2d
    base0
    syl6eqr
    nsyl2
    adantl
    cS
    @4
    cG
    cH
    cvv
    subgabl.h
    @4
    eqid
    #
    ressplusg
    syl
    @0
    @1
    simpr
    @2
    @0
    vx
    cv
    #
    @3
    wcel
    @10
    cG
    cbs
    cfv
    #
    wcel
    vy
    cv
    #
    @3
    wcel
    @12
    @11
    wcel
    @10
    @12
    @4
    co
    @12
    @10
    @4
    co
    wceq
    @0
    @1
    simpl
    @3
    @11
    @10
    cS
    @11
    cH
    cG
    subgabl.h
    @11
    eqid
    #
    ressbasss
    #
    sseli
    @3
    @11
    @12
    @14
    sseli
    @11
    @4
    cG
    @10
    @12
    @13
    @9
    cmncom
    syl3an
    iscmnd
end
