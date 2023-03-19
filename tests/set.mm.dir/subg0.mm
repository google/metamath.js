include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "c0g.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "cgrp.mm"
include "cbs.mm"
include "subggrp.mm"
include "grpidcl.mm"
include "syl.mm"
include "grplid.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "wb.mm"
include "subgrcl.mm"
include "subgss.mm"
include "subgbas.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "grpid.mm"
include "mpbid.mm"

theorem subg0
  let cS: class S
  let cG: class G
  let cH: class H
  let c.0: class .0.
  assume subg0.h: |- H = ( G |`s S )
  assume subg0.i: |- .0. = ( 0g ` G )


  assert |- ( S e. ( SubGrp ` G ) -> .0. = ( 0g ` H ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cH
    c0g
    cfv
    #
    @2
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    wceq
    #
    c.0
    @2
    wceq
    #
    @1
    @4
    @2
    @2
    cH
    cplusg
    cfv
    #
    co
    #
    @2
    @1
    @3
    @7
    @2
    @2
    cS
    @3
    cG
    cH
    @0
    subg0.h
    @3
    eqid
    #
    ressplusg
    oveqd
    @1
    cH
    cgrp
    wcel
    #
    @2
    cH
    cbs
    cfv
    #
    wcel
    #
    @8
    @2
    wceq
    cS
    cG
    cH
    subg0.h
    subggrp
    #
    @1
    @10
    @12
    @13
    @11
    cH
    @2
    @11
    eqid
    #
    @2
    eqid
    #
    grpidcl
    syl
    #
    @11
    @7
    cH
    @2
    @2
    @14
    @7
    eqid
    @15
    grplid
    syl2anc
    eqtrd
    @1
    cG
    cgrp
    wcel
    @2
    cG
    cbs
    cfv
    #
    wcel
    @5
    @6
    wb
    cS
    cG
    subgrcl
    @1
    cS
    @17
    @2
    @17
    cS
    cG
    @17
    eqid
    #
    subgss
    @1
    @2
    @11
    cS
    @16
    cS
    cG
    cH
    subg0.h
    subgbas
    eleqtrrd
    sseldd
    @17
    @3
    cG
    @2
    c.0
    @18
    @9
    subg0.i
    grpid
    syl2anc
    mpbid
end
