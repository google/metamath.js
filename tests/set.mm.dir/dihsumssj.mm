include "cfv.mm"
include "co.mm"
include "cdjh.mm"
include "cbs.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "dihss.mm"
include "syl2anc.mm"
include "djhsumss.mm"
include "wceq.mm"
include "djhlj.mm"
include "syl12anc.mm"
include "sseqtr4d.mm"

theorem dihsumssj
  let wph: wff ph
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihsumssj.b: |- B = ( Base ` K )
  assume dihsumssj.h: |- H = ( LHyp ` K )
  assume dihsumssj.j: |- .\/ = ( join ` K )
  assume dihsumssj.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihsumssj.p: |- .(+) = ( LSSum ` U )
  assume dihsumssj.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihsumssj.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihsumssj.x: |- ( ph -> X e. B )
  assume dihsumssj.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( I ` X ) .(+) ( I ` Y ) ) C_ ( I ` ( X .\/ Y ) ) )

  proof
    wph
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    c.po
    co
    @0
    @1
    cW
    cK
    cdjh
    cfv
    cfv
    #
    co
    #
    cX
    cY
    c.or
    co
    cI
    cfv
    #
    wph
    c.po
    cU
    cH
    @2
    cK
    cU
    cbs
    cfv
    #
    cW
    @0
    @1
    dihsumssj.h
    dihsumssj.u
    @5
    eqid
    #
    dihsumssj.p
    @2
    eqid
    #
    dihsumssj.k
    wph
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
    #
    @0
    @5
    wss
    dihsumssj.k
    dihsumssj.x
    cB
    cU
    cH
    cI
    cK
    @5
    cW
    cX
    dihsumssj.b
    dihsumssj.h
    dihsumssj.i
    dihsumssj.u
    @6
    dihss
    syl2anc
    wph
    @8
    cY
    cB
    wcel
    #
    @1
    @5
    wss
    dihsumssj.k
    dihsumssj.y
    cB
    cU
    cH
    cI
    cK
    @5
    cW
    cY
    dihsumssj.b
    dihsumssj.h
    dihsumssj.i
    dihsumssj.u
    @6
    dihss
    syl2anc
    djhsumss
    wph
    @8
    @9
    @10
    @4
    @3
    wceq
    dihsumssj.k
    dihsumssj.x
    dihsumssj.y
    cB
    cH
    cI
    @2
    c.or
    cK
    cW
    cX
    cY
    dihsumssj.b
    dihsumssj.j
    dihsumssj.h
    dihsumssj.i
    @7
    djhlj
    syl12anc
    sseqtr4d
end
