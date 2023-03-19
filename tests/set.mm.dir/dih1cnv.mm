include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "dih1.mm"
include "fveq2d.mm"
include "cbs.mm"
include "wceq.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "eqid.mm"
include "op1cl.mm"
include "syl.mm"
include "dihcnvid1.mm"
include "mpdan.mm"
include "eqtr3d.mm"

theorem dih1cnv
  let cU: class U
  let c.1: class .1.
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  assume dih1cnv.h: |- H = ( LHyp ` K )
  assume dih1cnv.m: |- .1. = ( 1. ` K )
  assume dih1cnv.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1cnv.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1cnv.v: |- V = ( Base ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> ( `' I ` V ) = .1. )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    c.1
    cI
    cfv
    #
    cI
    ccnv
    #
    cfv
    #
    cV
    @4
    cfv
    c.1
    @2
    @3
    cV
    @4
    cU
    c.1
    cH
    cI
    cK
    cV
    cW
    dih1cnv.m
    dih1cnv.h
    dih1cnv.i
    dih1cnv.u
    dih1cnv.v
    dih1
    fveq2d
    @2
    c.1
    cK
    cbs
    cfv
    #
    wcel
    #
    @5
    c.1
    wceq
    @2
    cK
    cops
    wcel
    #
    @7
    @0
    @8
    @1
    cK
    hlop
    adantr
    @6
    c.1
    cK
    @6
    eqid
    #
    dih1cnv.m
    op1cl
    syl
    @6
    cH
    cI
    cK
    cW
    c.1
    @9
    dih1cnv.h
    dih1cnv.i
    dihcnvid1
    mpdan
    eqtr3d
end
