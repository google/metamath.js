include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "cgrp.mm"
include "cbs.mm"
include "subggrp.mm"
include "adantr.mm"
include "subgbas.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "eqid.mm"
include "grprinv.mm"
include "syl2anc.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "subg0.mm"
include "3eqtr4d.mm"
include "wb.mm"
include "subgrcl.mm"
include "subgss.mm"
include "sselda.mm"
include "wi.mm"
include "grpinvcl.mm"
include "ex.mm"
include "syl.mm"
include "3imtr4d.mm"
include "imp.mm"
include "syldan.mm"
include "grpinvid1.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem subginv
  let cS: class S
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cX: class X
  assume subg0.h: |- H = ( G |`s S )
  assume subginv.i: |- I = ( invg ` G )
  assume subginv.j: |- J = ( invg ` H )


  assert |- ( ( S e. ( SubGrp ` G ) /\ X e. S ) -> ( I ` X ) = ( J ` X ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cX
    cS
    wcel
    #
    wa
    #
    cX
    cI
    cfv
    cX
    cJ
    cfv
    #
    wceq
    #
    cX
    @4
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    @3
    cX
    @4
    cH
    cplusg
    cfv
    #
    co
    #
    cH
    c0g
    cfv
    #
    @7
    @8
    @3
    cH
    cgrp
    wcel
    #
    cX
    cH
    cbs
    cfv
    #
    wcel
    #
    @11
    @12
    wceq
    @1
    @13
    @2
    cS
    cG
    cH
    subg0.h
    subggrp
    #
    adantr
    @1
    @2
    @15
    @1
    cS
    @14
    cX
    cS
    cG
    cH
    subg0.h
    subgbas
    #
    eleq2d
    #
    biimpa
    @14
    @10
    cH
    cJ
    cX
    @12
    @14
    eqid
    #
    @10
    eqid
    @12
    eqid
    subginv.j
    grprinv
    syl2anc
    @3
    @6
    @10
    cX
    @4
    @1
    @6
    @10
    wceq
    @2
    cS
    @6
    cG
    cH
    @0
    subg0.h
    @6
    eqid
    #
    ressplusg
    adantr
    oveqd
    @1
    @8
    @12
    wceq
    @2
    cS
    cG
    cH
    @8
    subg0.h
    @8
    eqid
    #
    subg0
    adantr
    3eqtr4d
    @3
    cG
    cgrp
    wcel
    #
    cX
    cG
    cbs
    cfv
    #
    wcel
    @4
    @23
    wcel
    #
    @5
    @9
    wb
    @1
    @22
    @2
    cS
    cG
    subgrcl
    adantr
    @1
    cS
    @23
    cX
    @23
    cS
    cG
    @23
    eqid
    #
    subgss
    #
    sselda
    @1
    @2
    @4
    cS
    wcel
    #
    @24
    @1
    @2
    @27
    @1
    @15
    @4
    @14
    wcel
    #
    @2
    @27
    @1
    @13
    @15
    @28
    wi
    @16
    @13
    @15
    @28
    @14
    cH
    cJ
    cX
    @19
    subginv.j
    grpinvcl
    ex
    syl
    @18
    @1
    cS
    @14
    @4
    @17
    eleq2d
    3imtr4d
    imp
    @1
    cS
    @23
    @4
    @26
    sselda
    syldan
    @23
    @6
    cG
    cI
    cX
    @4
    @8
    @25
    @20
    @21
    subginv.i
    grpinvid1
    syl3anc
    mpbird
end
