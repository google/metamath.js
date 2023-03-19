include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "cdia.mm"
include "cltrn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "eqid.mm"
include "dibval2.mm"
include "3adant3.mm"
include "3adant2.mm"
include "sseq12d.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "dibn0.mm"
include "eqnetrrd.mm"
include "ssxpb.mm"
include "syl.mm"
include "ssid.mm"
include "biantru.mm"
include "diaord.mm"
include "syl5bbr.mm"
include "3bitrd.mm"

theorem dibord
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume dib11.b: |- B = ( Base ` K )
  assume dib11.l: |- .<_ = ( le ` K )
  assume dib11.h: |- H = ( LHyp ` K )
  assume dib11.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) -> ( ( I ` X ) C_ ( I ` Y ) <-> X .<_ Y ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    #
    cY
    cB
    wcel
    cY
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    wss
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
    cfv
    #
    cid
    cB
    cres
    cmpt
    #
    csn
    #
    cxp
    #
    cY
    @6
    cfv
    #
    @10
    cxp
    #
    wss
    #
    @7
    @12
    wss
    #
    @10
    @10
    wss
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    @3
    @4
    @11
    @5
    @13
    @0
    @1
    @4
    @11
    wceq
    @2
    cB
    @8
    vf
    cH
    cI
    @6
    cK
    c.le
    chlt
    cW
    cX
    @9
    dib11.b
    dib11.l
    dib11.h
    @8
    eqid
    #
    @9
    eqid
    #
    @6
    eqid
    #
    dib11.i
    dibval2
    3adant3
    #
    @0
    @2
    @5
    @13
    wceq
    @1
    cB
    @8
    vf
    cH
    cI
    @6
    cK
    c.le
    chlt
    cW
    cY
    @9
    dib11.b
    dib11.l
    dib11.h
    @19
    @20
    @21
    dib11.i
    dibval2
    3adant2
    sseq12d
    @3
    @11
    c0
    wne
    @14
    @17
    wb
    @3
    @4
    @11
    c0
    @22
    @0
    @1
    @4
    c0
    wne
    @2
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    dib11.b
    dib11.l
    dib11.h
    dib11.i
    dibn0
    3adant3
    eqnetrrd
    @7
    @10
    @12
    @10
    ssxpb
    syl
    @17
    @15
    @3
    @18
    @16
    @15
    @10
    ssid
    biantru
    cB
    cH
    @6
    cK
    c.le
    cW
    cX
    cY
    dib11.b
    dib11.l
    dib11.h
    @21
    diaord
    syl5bbr
    3bitrd
end
