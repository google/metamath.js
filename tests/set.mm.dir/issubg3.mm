include "cgrp.mm"
include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "csubg.mm"
include "csubmnd.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "eqid.mm"
include "subg0cl.mm"
include "a1i.mm"
include "subm0cl.mm"
include "adantr.mm"
include "wb.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cplusg.mm"
include "co.mm"
include "w3a.mm"
include "ne0i.mm"
include "id.mm"
include "2thd.mm"
include "adantl.mm"
include "r19.26.mm"
include "3anbi23d.mm"
include "anass.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "3bitr4ri.mm"
include "syl6bb.mm"
include "issubg2.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "issubm.mm"
include "syl.mm"
include "anbi1d.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem issubg3
  let vx: setvar x
  let cS: class S
  let cG: class G
  let cI: class I
  let vy: setvar y
  assume issubg3.i: |- I = ( invg ` G )

  disjoint G x
  disjoint I x
  disjoint S x
  disjoint G y
  disjoint x y
  disjoint I y
  disjoint S y
  assert |- ( G e. Grp -> ( S e. ( SubGrp ` G ) <-> ( S e. ( SubMnd ` G ) /\ A. x e. S ( I ` x ) e. S ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cG
    c0g
    cfv
    #
    cS
    wcel
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    cS
    cG
    csubmnd
    cfv
    wcel
    #
    vx
    cv
    #
    cI
    cfv
    cS
    wcel
    #
    vx
    cS
    wral
    #
    wa
    #
    @3
    @2
    wi
    @0
    cS
    cG
    @1
    @1
    eqid
    #
    subg0cl
    a1i
    @8
    @2
    wi
    @0
    @4
    @2
    @7
    cS
    cG
    @1
    @9
    subm0cl
    adantr
    a1i
    @0
    @2
    @3
    @8
    wb
    @0
    @2
    wa
    #
    cS
    cG
    cbs
    cfv
    #
    wss
    #
    cS
    c0
    wne
    #
    @5
    vy
    cv
    cG
    cplusg
    cfv
    #
    co
    cS
    wcel
    vy
    cS
    wral
    #
    @6
    wa
    vx
    cS
    wral
    #
    w3a
    #
    @12
    @2
    @15
    vx
    cS
    wral
    #
    w3a
    #
    @7
    wa
    #
    @3
    @8
    @10
    @17
    @12
    @2
    @18
    @7
    wa
    #
    w3a
    #
    @20
    @10
    @13
    @2
    @16
    @21
    @12
    @2
    @13
    @2
    wb
    @0
    @2
    @13
    @2
    cS
    @1
    ne0i
    @2
    id
    2thd
    adantl
    @16
    @21
    wb
    @10
    @15
    @6
    vx
    cS
    r19.26
    a1i
    3anbi23d
    @12
    @2
    wa
    #
    @18
    wa
    #
    @7
    wa
    @23
    @21
    wa
    @20
    @22
    @23
    @18
    @7
    anass
    @19
    @24
    @7
    @12
    @2
    @18
    df-3an
    anbi1i
    @12
    @2
    @21
    df-3an
    3bitr4ri
    syl6bb
    @0
    @3
    @17
    wb
    @2
    vx
    vy
    @11
    @14
    cS
    cG
    cI
    @11
    eqid
    #
    @14
    eqid
    #
    issubg3.i
    issubg2
    adantr
    @0
    @8
    @20
    wb
    @2
    @0
    @4
    @19
    @7
    @0
    cG
    cmnd
    wcel
    @4
    @19
    wb
    cG
    grpmnd
    vx
    vy
    @11
    @14
    cS
    cG
    @1
    @25
    @9
    @26
    issubm
    syl
    anbi1d
    adantr
    3bitr4d
    ex
    pm5.21ndd
end
