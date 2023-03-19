include "cp1.mm"
include "cfv.mm"
include "cmee.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "cops.mm"
include "simpld.mm"
include "hlop.mm"
include "syl.mm"
include "eqid.mm"
include "op1cl.mm"
include "atbase.mm"
include "ople1.mm"
include "syl2anc.mm"
include "col.mm"
include "hlol.mm"
include "olm12.mm"
include "simprd.mm"
include "eqbrtrd.mm"
include "dihjatc3.mm"
include "syl312anc.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"

theorem dihjatc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  assume dihjatc.b: |- B = ( Base ` K )
  assume dihjatc.l: |- .<_ = ( le ` K )
  assume dihjatc.h: |- H = ( LHyp ` K )
  assume dihjatc.j: |- .\/ = ( join ` K )
  assume dihjatc.a: |- A = ( Atoms ` K )
  assume dihjatc.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjatc.s: |- .(+) = ( LSSum ` U )
  assume dihjatc.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjatc.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjatc.x: |- ( ph -> ( X e. B /\ X .<_ W ) )
  assume dihjatc.p: |- ( ph -> ( P e. A /\ -. P .<_ W ) )


  assert |- ( ph -> ( I ` ( X .\/ P ) ) = ( ( I ` X ) .(+) ( I ` P ) ) )

  proof
    wph
    cK
    cp1
    cfv
    #
    cX
    cK
    cmee
    cfv
    #
    co
    #
    cP
    c.or
    co
    #
    cI
    cfv
    #
    @2
    cI
    cfv
    #
    cP
    cI
    cfv
    #
    c.po
    co
    #
    cX
    cP
    c.or
    co
    #
    cI
    cfv
    cX
    cI
    cfv
    #
    @6
    c.po
    co
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
    @0
    cB
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    cP
    @0
    c.le
    wbr
    #
    @2
    cW
    c.le
    wbr
    @4
    @7
    wceq
    dihjatc.k
    wph
    cK
    cops
    wcel
    #
    @12
    wph
    @10
    @17
    wph
    @10
    @11
    dihjatc.k
    simpld
    #
    cK
    hlop
    syl
    #
    cB
    @0
    cK
    dihjatc.b
    @0
    eqid
    #
    op1cl
    syl
    wph
    @13
    cX
    cW
    c.le
    wbr
    #
    dihjatc.x
    simpld
    #
    dihjatc.p
    wph
    @17
    cP
    cB
    wcel
    #
    @16
    @19
    wph
    @14
    @23
    wph
    @14
    @15
    dihjatc.p
    simpld
    cA
    cB
    cP
    cK
    dihjatc.b
    dihjatc.a
    atbase
    syl
    cB
    @0
    cK
    c.le
    cP
    dihjatc.b
    dihjatc.l
    @20
    ople1
    syl2anc
    wph
    @2
    cX
    cW
    c.le
    wph
    cK
    col
    wcel
    #
    @13
    @2
    cX
    wceq
    wph
    @10
    @24
    @18
    cK
    hlol
    syl
    @22
    cB
    @0
    cK
    @1
    cX
    dihjatc.b
    @1
    eqid
    #
    @20
    olm12
    syl2anc
    #
    wph
    @13
    @21
    dihjatc.x
    simprd
    eqbrtrd
    cA
    cB
    c.po
    cP
    cU
    cH
    cI
    c.or
    cK
    c.le
    @1
    cW
    @0
    cX
    dihjatc.b
    dihjatc.l
    dihjatc.h
    dihjatc.j
    @25
    dihjatc.a
    dihjatc.u
    dihjatc.s
    dihjatc.i
    dihjatc3
    syl312anc
    wph
    @3
    @8
    cI
    wph
    @2
    cX
    cP
    c.or
    @26
    oveq1d
    fveq2d
    wph
    @5
    @9
    @6
    c.po
    wph
    @2
    cX
    cI
    @26
    fveq2d
    oveq1d
    3eqtr3d
end
