include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "ctendo.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "eqid.mm"
include "erngfplus.mm"
include "oveqd.mm"
include "tendo0cl.mm"
include "tendo0pl.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "cgrp.mm"
include "cbs.mm"
include "wb.mm"
include "crg.mm"
include "eringring.mm"
include "ringgrp.mm"
include "syl.mm"
include "erngbase.mm"
include "eleqtrrd.mm"
include "grpid.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem erng0g
  let cB: class B
  let cD: class D
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vt: setvar t
  assume erng0g.b: |- B = ( Base ` K )
  assume erng0g.h: |- H = ( LHyp ` K )
  assume erng0g.t: |- T = ( ( LTrn ` K ) ` W )
  assume erng0g.d: |- D = ( ( EDRing ` K ) ` W )
  assume erng0g.o: |- O = ( f e. T |-> ( _I |` B ) )
  assume erng0g.z: |- .0. = ( 0g ` D )

  disjoint B f
  disjoint H f
  disjoint K f
  disjoint T f
  disjoint W f
  disjoint f s
  disjoint f t
  disjoint s t
  disjoint K s
  disjoint K t
  disjoint T s
  disjoint T t
  disjoint W s
  disjoint W t
  assert |- ( ( K e. HL /\ W e. H ) -> .0. = O )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cO
    cO
    cD
    cplusg
    cfv
    #
    co
    #
    cO
    wceq
    #
    c.0
    cO
    wceq
    #
    @0
    @2
    cO
    cO
    vs
    vt
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @5
    vf
    cT
    vf
    cv
    #
    vs
    cv
    cfv
    @6
    vt
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    #
    cO
    @0
    @1
    @7
    cO
    cO
    vt
    cD
    @1
    cT
    vf
    @5
    cH
    cK
    chlt
    cW
    vs
    erng0g.h
    erng0g.t
    @5
    eqid
    #
    erng0g.d
    @1
    eqid
    #
    erngfplus
    oveqd
    @0
    cO
    @5
    wcel
    @8
    cO
    wceq
    cB
    cT
    vf
    @5
    cH
    cK
    cO
    cW
    erng0g.b
    erng0g.h
    erng0g.t
    @9
    erng0g.o
    tendo0cl
    #
    vt
    cB
    @7
    cO
    cT
    vf
    @5
    cH
    cK
    cO
    cW
    vs
    erng0g.b
    erng0g.h
    erng0g.t
    @9
    erng0g.o
    @7
    eqid
    tendo0pl
    mpdan
    eqtrd
    @0
    cD
    cgrp
    wcel
    #
    cO
    cD
    cbs
    cfv
    #
    wcel
    @3
    @4
    wb
    @0
    cD
    crg
    wcel
    @12
    cD
    cH
    cK
    cW
    erng0g.h
    erng0g.d
    eringring
    cD
    ringgrp
    syl
    @0
    cO
    @5
    @13
    @11
    @13
    cD
    cT
    @5
    cH
    cK
    chlt
    cW
    erng0g.h
    erng0g.t
    @9
    erng0g.d
    @13
    eqid
    #
    erngbase
    eleqtrrd
    @13
    @1
    cD
    cO
    c.0
    @14
    @10
    erng0g.z
    grpid
    syl2anc
    mpbid
end
