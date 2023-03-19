include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "dih0.mm"
include "fveq2d.mm"
include "cbs.mm"
include "wceq.mm"
include "cal.mm"
include "hlatl.mm"
include "adantr.mm"
include "eqid.mm"
include "atl0cl.mm"
include "syl.mm"
include "dihcnvid1.mm"
include "mpdan.mm"
include "eqtr3d.mm"

theorem dih0cnv
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  assume dih0cnv.h: |- H = ( LHyp ` K )
  assume dih0cnv.o: |- .0. = ( 0. ` K )
  assume dih0cnv.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih0cnv.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih0cnv.z: |- Z = ( 0g ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> ( `' I ` { Z } ) = .0. )

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
    c.0
    cI
    cfv
    #
    cI
    ccnv
    #
    cfv
    #
    cZ
    csn
    #
    @4
    cfv
    c.0
    @2
    @3
    @6
    @4
    cU
    cH
    cI
    cK
    cZ
    cW
    c.0
    dih0cnv.o
    dih0cnv.h
    dih0cnv.i
    dih0cnv.u
    dih0cnv.z
    dih0
    fveq2d
    @2
    c.0
    cK
    cbs
    cfv
    #
    wcel
    #
    @5
    c.0
    wceq
    @2
    cK
    cal
    wcel
    #
    @8
    @0
    @9
    @1
    cK
    hlatl
    adantr
    @7
    cK
    c.0
    @7
    eqid
    #
    dih0cnv.o
    atl0cl
    syl
    @7
    cH
    cI
    cK
    cW
    c.0
    @10
    dih0cnv.h
    dih0cnv.i
    dihcnvid1
    mpdan
    eqtr3d
end
