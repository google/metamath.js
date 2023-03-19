include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cdia.mm"
include "cltrn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "c0.mm"
include "eqid.mm"
include "dibval2.mm"
include "wne.mm"
include "dian0.mm"
include "fvex.mm"
include "mptex.mm"
include "snnz.mm"
include "jctir.mm"
include "xpnz.mm"
include "sylib.mm"
include "eqnetrd.mm"

theorem dibn0
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vf: setvar f
  assume dibn0.b: |- B = ( Base ` K )
  assume dibn0.l: |- .<_ = ( le ` K )
  assume dibn0.h: |- H = ( LHyp ` K )
  assume dibn0.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) =/= (/) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    wa
    #
    cX
    cI
    cfv
    cX
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    vf
    cW
    cK
    cltrn
    cfv
    #
    cfv
    #
    cid
    cB
    cres
    #
    cmpt
    #
    csn
    #
    cxp
    #
    c0
    cB
    @4
    vf
    cH
    cI
    @1
    cK
    c.le
    chlt
    cW
    cX
    @6
    dibn0.b
    dibn0.l
    dibn0.h
    @4
    eqid
    @6
    eqid
    @1
    eqid
    #
    dibn0.i
    dibval2
    @0
    @2
    c0
    wne
    #
    @7
    c0
    wne
    #
    wa
    @8
    c0
    wne
    @0
    @10
    @11
    cB
    cH
    @1
    cK
    c.le
    cW
    cX
    dibn0.b
    dibn0.l
    dibn0.h
    @9
    dian0
    @6
    vf
    @4
    @5
    cW
    @3
    fvex
    mptex
    snnz
    jctir
    @2
    @7
    xpnz
    sylib
    eqnetrd
end
