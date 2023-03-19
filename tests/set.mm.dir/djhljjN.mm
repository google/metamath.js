include "co.mm"
include "cfv.mm"
include "ccnv.mm"
include "wceq.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "djhlj.mm"
include "syl12anc.mm"
include "crn.mm"
include "cdvh.mm"
include "cbs.mm"
include "wss.mm"
include "dihcl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "dihrnss.mm"
include "djhcl.mm"
include "dihcnvid2.mm"
include "eqtr4d.mm"
include "wb.mm"
include "clat.mm"
include "simpld.mm"
include "hllat.mm"
include "syl.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "dihcnvcl.mm"
include "dih11.mm"
include "mpbid.mm"

theorem djhljjN
  let wph: wff ph
  let cB: class B
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhlj.b: |- B = ( Base ` K )
  assume djhlj.k: |- .\/ = ( join ` K )
  assume djhlj.h: |- H = ( LHyp ` K )
  assume djhlj.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djhlj.j: |- J = ( ( joinH ` K ) ` W )
  assume djhljj.w: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhljj.x: |- ( ph -> X e. B )
  assume djhljj.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X .\/ Y ) = ( `' I ` ( ( I ` X ) J ( I ` Y ) ) ) )

  proof
    wph
    cX
    cY
    c.or
    co
    #
    cI
    cfv
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cJ
    co
    #
    cI
    ccnv
    cfv
    #
    cI
    cfv
    #
    wceq
    #
    @0
    @5
    wceq
    #
    wph
    @1
    @4
    @6
    wph
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
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @1
    @4
    wceq
    djhljj.w
    djhljj.x
    djhljj.y
    cB
    cH
    cI
    cJ
    c.or
    cK
    cW
    cX
    cY
    djhlj.b
    djhlj.k
    djhlj.h
    djhlj.i
    djhlj.j
    djhlj
    syl12anc
    wph
    @11
    @4
    cI
    crn
    #
    wcel
    #
    @6
    @4
    wceq
    djhljj.w
    wph
    @11
    @2
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    wss
    #
    @3
    @17
    wss
    #
    @15
    djhljj.w
    wph
    @11
    @2
    @14
    wcel
    #
    @18
    djhljj.w
    wph
    @11
    @12
    @20
    djhljj.w
    djhljj.x
    cB
    cH
    cI
    cK
    cW
    cX
    djhlj.b
    djhlj.h
    djhlj.i
    dihcl
    syl2anc
    @16
    cH
    cI
    cK
    @17
    cW
    @2
    djhlj.h
    @16
    eqid
    #
    djhlj.i
    @17
    eqid
    #
    dihrnss
    syl2anc
    wph
    @11
    @3
    @14
    wcel
    #
    @19
    djhljj.w
    wph
    @11
    @13
    @23
    djhljj.w
    djhljj.y
    cB
    cH
    cI
    cK
    cW
    cY
    djhlj.b
    djhlj.h
    djhlj.i
    dihcl
    syl2anc
    @16
    cH
    cI
    cK
    @17
    cW
    @3
    djhlj.h
    @21
    djhlj.i
    @22
    dihrnss
    syl2anc
    @16
    cH
    cI
    cJ
    cK
    @17
    cW
    @2
    @3
    djhlj.h
    djhlj.i
    @21
    @22
    djhlj.j
    djhcl
    syl12anc
    #
    cH
    cI
    cK
    cW
    @4
    djhlj.h
    djhlj.i
    dihcnvid2
    syl2anc
    eqtr4d
    wph
    @11
    @0
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @7
    @8
    wb
    djhljj.w
    wph
    cK
    clat
    wcel
    #
    @12
    @13
    @25
    wph
    @9
    @27
    wph
    @9
    @10
    djhljj.w
    simpld
    cK
    hllat
    syl
    djhljj.x
    djhljj.y
    cB
    c.or
    cK
    cX
    cY
    djhlj.b
    djhlj.k
    latjcl
    syl3anc
    wph
    @11
    @15
    @26
    djhljj.w
    @24
    cB
    cH
    cI
    cK
    cW
    @4
    djhlj.b
    djhlj.h
    djhlj.i
    dihcnvcl
    syl2anc
    cB
    cH
    cI
    cK
    cW
    @0
    @5
    djhlj.b
    djhlj.h
    djhlj.i
    dih11
    syl3anc
    mpbid
end
