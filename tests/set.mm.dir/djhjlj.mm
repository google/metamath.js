include "ccnv.mm"
include "cfv.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "wceq.mm"
include "crn.mm"
include "eqid.mm"
include "dihcnvcl.mm"
include "syl2anc.mm"
include "djhlj.mm"
include "syl12anc.mm"
include "dihcnvid2.mm"
include "oveq12d.mm"
include "eqtr2d.mm"

theorem djhjlj
  let wph: wff ph
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhj.k: |- .\/ = ( join ` K )
  assume djhj.h: |- H = ( LHyp ` K )
  assume djhj.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djhj.j: |- J = ( ( joinH ` K ) ` W )
  assume djhj.w: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhj.x: |- ( ph -> X e. ran I )
  assume djhj.y: |- ( ph -> Y e. ran I )


  assert |- ( ph -> ( X J Y ) = ( I ` ( ( `' I ` X ) .\/ ( `' I ` Y ) ) ) )

  proof
    wph
    cX
    cI
    ccnv
    #
    cfv
    #
    cY
    @0
    cfv
    #
    c.or
    co
    cI
    cfv
    #
    @1
    cI
    cfv
    #
    @2
    cI
    cfv
    #
    cJ
    co
    #
    cX
    cY
    cJ
    co
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cK
    cbs
    cfv
    #
    wcel
    #
    @2
    @8
    wcel
    #
    @3
    @6
    wceq
    djhj.w
    wph
    @7
    cX
    cI
    crn
    #
    wcel
    #
    @9
    djhj.w
    djhj.x
    @8
    cH
    cI
    cK
    cW
    cX
    @8
    eqid
    #
    djhj.h
    djhj.i
    dihcnvcl
    syl2anc
    wph
    @7
    cY
    @11
    wcel
    #
    @10
    djhj.w
    djhj.y
    @8
    cH
    cI
    cK
    cW
    cY
    @13
    djhj.h
    djhj.i
    dihcnvcl
    syl2anc
    @8
    cH
    cI
    cJ
    c.or
    cK
    cW
    @1
    @2
    @13
    djhj.k
    djhj.h
    djhj.i
    djhj.j
    djhlj
    syl12anc
    wph
    @4
    cX
    @5
    cY
    cJ
    wph
    @7
    @12
    @4
    cX
    wceq
    djhj.w
    djhj.x
    cH
    cI
    cK
    cW
    cX
    djhj.h
    djhj.i
    dihcnvid2
    syl2anc
    wph
    @7
    @14
    @5
    cY
    wceq
    djhj.w
    djhj.y
    cH
    cI
    cK
    cW
    cY
    djhj.h
    djhj.i
    dihcnvid2
    syl2anc
    oveq12d
    eqtr2d
end
