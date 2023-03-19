include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "csn.mm"
include "cltrn.mm"
include "cmpt.mm"
include "cxp.mm"
include "cop.mm"
include "cvv.mm"
include "fvex.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "mptex.mm"
include "xpsn.mm"
include "cdia.mm"
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
include "dibval2.mm"
include "syl12anc.mm"
include "dia0.mm"
include "xpeq1d.mm"
include "eqtrd.mm"
include "dvh0g.mm"
include "sneqd.mm"
include "3eqtr4a.mm"

theorem dib0
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  assume dib0.z: |- .0. = ( 0. ` K )
  assume dib0.h: |- H = ( LHyp ` K )
  assume dib0.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dib0.u: |- U = ( ( DVecH ` K ) ` W )
  assume dib0.o: |- O = ( 0g ` U )


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
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    csn
    #
    vf
    cW
    cK
    cltrn
    cfv
    #
    cfv
    #
    @4
    cmpt
    #
    csn
    #
    cxp
    #
    @4
    @8
    cop
    #
    csn
    c.0
    cI
    cfv
    #
    cO
    csn
    @4
    @8
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    cK
    cbs
    fvex
    @3
    cvv
    resiexg
    ax-mp
    vf
    @7
    @4
    cW
    @6
    fvex
    mptex
    xpsn
    @2
    @12
    c.0
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    @9
    cxp
    #
    @10
    @2
    @2
    c.0
    @3
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
    @12
    @15
    wceq
    @2
    id
    @2
    cK
    cops
    wcel
    #
    @16
    @0
    @19
    @1
    cK
    hlop
    #
    adantr
    @3
    cK
    c.0
    @3
    eqid
    #
    dib0.z
    op0cl
    syl
    @0
    @19
    cW
    @3
    wcel
    @18
    @1
    @20
    @3
    cH
    cK
    cW
    @21
    dib0.h
    lhpbase
    @3
    cK
    @17
    cW
    c.0
    @21
    @17
    eqid
    #
    dib0.z
    op0le
    syl2an
    @3
    @7
    vf
    cH
    cI
    @13
    cK
    @17
    chlt
    cW
    c.0
    @8
    @21
    @22
    dib0.h
    @7
    eqid
    #
    @8
    eqid
    #
    @13
    eqid
    #
    dib0.i
    dibval2
    syl12anc
    @2
    @14
    @5
    @9
    @3
    cH
    @13
    cK
    cW
    c.0
    @21
    dib0.z
    dib0.h
    @25
    dia0
    xpeq1d
    eqtrd
    @2
    cO
    @11
    @3
    @7
    cU
    vf
    cH
    cK
    @8
    cW
    cO
    @21
    dib0.h
    @23
    dib0.u
    dib0.o
    @24
    dvh0g
    sneqd
    3eqtr4a
end
