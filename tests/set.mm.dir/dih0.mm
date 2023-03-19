include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cdib.mm"
include "csn.mm"
include "cbs.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "id.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "eqid.mm"
include "op0cl.mm"
include "syl.mm"
include "lhpbase.mm"
include "op0le.mm"
include "syl2an.mm"
include "dihvalb.mm"
include "syl12anc.mm"
include "dib0.mm"
include "eqtrd.mm"

theorem dih0
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cO: class O
  let cW: class W
  let c.0: class .0.
  assume dih0.z: |- .0. = ( 0. ` K )
  assume dih0.h: |- H = ( LHyp ` K )
  assume dih0.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih0.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih0.o: |- O = ( 0g ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> ( I ` .0. ) = { O } )

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
    c.0
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    cO
    csn
    @2
    @2
    c.0
    cK
    cbs
    cfv
    #
    wcel
    #
    c.0
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @3
    @5
    wceq
    @2
    id
    @2
    cK
    cops
    wcel
    #
    @7
    @0
    @10
    @1
    cK
    hlop
    #
    adantr
    @6
    cK
    c.0
    @6
    eqid
    #
    dih0.z
    op0cl
    syl
    @0
    @10
    cW
    @6
    wcel
    @9
    @1
    @11
    @6
    cH
    cK
    cW
    @12
    dih0.h
    lhpbase
    @6
    cK
    @8
    cW
    c.0
    @12
    @8
    eqid
    #
    dih0.z
    op0le
    syl2an
    @6
    @4
    cH
    cI
    cK
    @8
    chlt
    cW
    c.0
    @12
    @13
    dih0.h
    dih0.i
    @4
    eqid
    #
    dihvalb
    syl12anc
    cU
    cH
    @4
    cK
    cO
    cW
    c.0
    dih0.z
    dih0.h
    @14
    dih0.u
    dih0.o
    dib0
    eqtrd
end
