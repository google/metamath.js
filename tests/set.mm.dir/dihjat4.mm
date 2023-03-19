include "ccnv.mm"
include "cfv.mm"
include "co.mm"
include "catm.mm"
include "cbs.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "dihcnvcl.mm"
include "syl2anc.mm"
include "dihlatat.mm"
include "dihjat3.mm"
include "wceq.mm"
include "dihcnvid2.mm"
include "dih1dimat.mm"
include "oveq12d.mm"
include "eqtr2d.mm"

theorem dihjat4
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihjat4.j: |- .\/ = ( join ` K )
  assume dihjat4.h: |- H = ( LHyp ` K )
  assume dihjat4.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjat4.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjat4.s: |- .(+) = ( LSSum ` U )
  assume dihjat4.a: |- A = ( LSAtoms ` U )
  assume dihjat4.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjat4.x: |- ( ph -> X e. ran I )
  assume dihjat4.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( X .(+) Q ) = ( I ` ( ( `' I ` X ) .\/ ( `' I ` Q ) ) ) )

  proof
    wph
    cX
    cI
    ccnv
    #
    cfv
    #
    cQ
    @0
    cfv
    #
    c.or
    co
    cI
    cfv
    @1
    cI
    cfv
    #
    @2
    cI
    cfv
    #
    c.po
    co
    cX
    cQ
    c.po
    co
    wph
    cK
    catm
    cfv
    #
    cK
    cbs
    cfv
    #
    @2
    c.po
    cU
    cH
    cI
    c.or
    cK
    cW
    @1
    @6
    eqid
    #
    dihjat4.h
    dihjat4.j
    @5
    eqid
    #
    dihjat4.u
    dihjat4.s
    dihjat4.i
    dihjat4.k
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
    cI
    crn
    #
    wcel
    #
    @1
    @6
    wcel
    dihjat4.k
    dihjat4.x
    @6
    cH
    cI
    cK
    cW
    cX
    @7
    dihjat4.h
    dihjat4.i
    dihcnvcl
    syl2anc
    wph
    @9
    cQ
    cA
    wcel
    #
    @2
    @5
    wcel
    dihjat4.k
    dihjat4.q
    @5
    cQ
    cU
    cH
    cI
    cK
    cA
    cW
    @8
    dihjat4.h
    dihjat4.u
    dihjat4.i
    dihjat4.a
    dihlatat
    syl2anc
    dihjat3
    wph
    @3
    cX
    @4
    cQ
    c.po
    wph
    @9
    @11
    @3
    cX
    wceq
    dihjat4.k
    dihjat4.x
    cH
    cI
    cK
    cW
    cX
    dihjat4.h
    dihjat4.i
    dihcnvid2
    syl2anc
    wph
    @9
    cQ
    @10
    wcel
    #
    @4
    cQ
    wceq
    dihjat4.k
    wph
    @9
    @12
    @13
    dihjat4.k
    dihjat4.q
    cA
    cQ
    cU
    cH
    cI
    cK
    cW
    dihjat4.h
    dihjat4.u
    dihjat4.i
    dihjat4.a
    dih1dimat
    syl2anc
    cH
    cI
    cK
    cW
    cQ
    dihjat4.h
    dihjat4.i
    dihcnvid2
    syl2anc
    oveq12d
    eqtr2d
end
