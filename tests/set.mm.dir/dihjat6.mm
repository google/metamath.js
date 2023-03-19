include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "dihjat4.mm"
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
include "dih1dimat.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "dihcnvid1.mm"
include "eqtrd.mm"

theorem dihjat6
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
  assume dihjat6.j: |- .\/ = ( join ` K )
  assume dihjat6.h: |- H = ( LHyp ` K )
  assume dihjat6.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjat6.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjat6.s: |- .(+) = ( LSSum ` U )
  assume dihjat6.a: |- A = ( LSAtoms ` U )
  assume dihjat6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjat6.x: |- ( ph -> X e. ran I )
  assume dihjat6.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( `' I ` ( X .(+) Q ) ) = ( ( `' I ` X ) .\/ ( `' I ` Q ) ) )

  proof
    wph
    cX
    cQ
    c.po
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
    cQ
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
    cA
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    cW
    cX
    dihjat6.j
    dihjat6.h
    dihjat6.i
    dihjat6.u
    dihjat6.s
    dihjat6.a
    dihjat6.k
    dihjat6.x
    dihjat6.q
    dihjat4
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
    dihjat6.k
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
    dihjat6.k
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
    dihjat6.k
    dihjat6.x
    @10
    cH
    cI
    cK
    cW
    cX
    @10
    eqid
    #
    dihjat6.h
    dihjat6.i
    dihcnvcl
    syl2anc
    wph
    @9
    cQ
    @15
    wcel
    #
    @14
    dihjat6.k
    wph
    @9
    cQ
    cA
    wcel
    @17
    dihjat6.k
    dihjat6.q
    cA
    cQ
    cU
    cH
    cI
    cK
    cW
    dihjat6.h
    dihjat6.u
    dihjat6.i
    dihjat6.a
    dih1dimat
    syl2anc
    @10
    cH
    cI
    cK
    cW
    cQ
    @16
    dihjat6.h
    dihjat6.i
    dihcnvcl
    syl2anc
    @10
    c.or
    cK
    @2
    @3
    @16
    dihjat6.j
    latjcl
    syl3anc
    @10
    cH
    cI
    cK
    cW
    @4
    @16
    dihjat6.h
    dihjat6.i
    dihcnvid1
    syl2anc
    eqtrd
end
