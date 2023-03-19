include "co.mm"
include "cfv.mm"
include "cdjh.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "atbase.mm"
include "syl.mm"
include "eqid.mm"
include "djhlj.mm"
include "syl12anc.mm"
include "clsa.mm"
include "crn.mm"
include "dihcl.mm"
include "syl2anc.mm"
include "dihatlat.mm"
include "dihjat2.mm"
include "eqtrd.mm"

theorem dihjat3
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
  let cW: class W
  let cX: class X
  assume dihjat3.b: |- B = ( Base ` K )
  assume dihjat3.h: |- H = ( LHyp ` K )
  assume dihjat3.j: |- .\/ = ( join ` K )
  assume dihjat3.a: |- A = ( Atoms ` K )
  assume dihjat3.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjat3.s: |- .(+) = ( LSSum ` U )
  assume dihjat3.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjat3.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjat3.x: |- ( ph -> X e. B )
  assume dihjat3.p: |- ( ph -> P e. A )


  assert |- ( ph -> ( I ` ( X .\/ P ) ) = ( ( I ` X ) .(+) ( I ` P ) ) )

  proof
    wph
    cX
    cP
    c.or
    co
    cI
    cfv
    #
    cX
    cI
    cfv
    #
    cP
    cI
    cfv
    #
    cW
    cK
    cdjh
    cfv
    cfv
    #
    co
    #
    @1
    @2
    c.po
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
    cX
    cB
    wcel
    #
    cP
    cB
    wcel
    #
    @0
    @4
    wceq
    dihjat3.k
    dihjat3.x
    wph
    cP
    cA
    wcel
    #
    @7
    dihjat3.p
    cA
    cB
    cP
    cK
    dihjat3.b
    dihjat3.a
    atbase
    syl
    cB
    cH
    cI
    @3
    c.or
    cK
    cW
    cX
    cP
    dihjat3.b
    dihjat3.j
    dihjat3.h
    dihjat3.i
    @3
    eqid
    #
    djhlj
    syl12anc
    wph
    cU
    clsa
    cfv
    #
    c.po
    @2
    cU
    cH
    cI
    @3
    cK
    cW
    @1
    dihjat3.h
    dihjat3.i
    @9
    dihjat3.u
    dihjat3.s
    @10
    eqid
    #
    dihjat3.k
    wph
    @5
    @6
    @1
    cI
    crn
    wcel
    dihjat3.k
    dihjat3.x
    cB
    cH
    cI
    cK
    cW
    cX
    dihjat3.b
    dihjat3.h
    dihjat3.i
    dihcl
    syl2anc
    wph
    @5
    @8
    @2
    @10
    wcel
    dihjat3.k
    dihjat3.p
    cA
    cP
    cU
    cH
    cI
    cK
    @10
    cW
    dihjat3.a
    dihjat3.h
    dihjat3.u
    dihjat3.i
    @11
    dihatlat
    syl2anc
    dihjat2
    eqtrd
end
