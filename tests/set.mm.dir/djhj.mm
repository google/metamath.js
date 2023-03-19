include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "djhjlj.mm"
include "fveq2d.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "wceq.mm"
include "clat.mm"
include "simpld.mm"
include "hllat.mm"
include "syl.mm"
include "crn.mm"
include "eqid.mm"
include "dihcnvcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "dihcnvid1.mm"
include "eqtrd.mm"

theorem djhj
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


  assert |- ( ph -> ( `' I ` ( X J Y ) ) = ( ( `' I ` X ) .\/ ( `' I ` Y ) ) )

  proof
    wph
    cX
    cY
    cJ
    co
    #
    cI
    ccnv
    #
    cfv
    cX
    @1
    cfv
    #
    cY
    @1
    cfv
    #
    c.or
    co
    #
    cI
    cfv
    #
    @1
    cfv
    #
    @4
    wph
    @0
    @5
    @1
    wph
    cH
    cI
    cJ
    c.or
    cK
    cW
    cX
    cY
    djhj.k
    djhj.h
    djhj.i
    djhj.j
    djhj.w
    djhj.x
    djhj.y
    djhjlj
    fveq2d
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
    @4
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @4
    wceq
    djhj.w
    wph
    cK
    clat
    wcel
    #
    @2
    @10
    wcel
    #
    @3
    @10
    wcel
    #
    @11
    wph
    @7
    @12
    wph
    @7
    @8
    djhj.w
    simpld
    cK
    hllat
    syl
    wph
    @9
    cX
    cI
    crn
    #
    wcel
    @13
    djhj.w
    djhj.x
    @10
    cH
    cI
    cK
    cW
    cX
    @10
    eqid
    #
    djhj.h
    djhj.i
    dihcnvcl
    syl2anc
    wph
    @9
    cY
    @15
    wcel
    @14
    djhj.w
    djhj.y
    @10
    cH
    cI
    cK
    cW
    cY
    @16
    djhj.h
    djhj.i
    dihcnvcl
    syl2anc
    @10
    c.or
    cK
    @2
    @3
    @16
    djhj.k
    latjcl
    syl3anc
    @10
    cH
    cI
    cK
    cW
    @4
    @16
    djhj.h
    djhj.i
    dihcnvid1
    syl2anc
    eqtrd
end
