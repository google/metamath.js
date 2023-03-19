include "co.mm"
include "cfv.mm"
include "ccnv.mm"
include "wceq.mm"
include "dihjat3.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "clsa.mm"
include "eqid.mm"
include "dihcl.mm"
include "syl2anc.mm"
include "dihatlat.mm"
include "dihsmatrn.mm"
include "dihcnvid2.mm"
include "eqtr4d.mm"
include "wb.mm"
include "clat.mm"
include "simpld.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "dihcnvcl.mm"
include "dih11.mm"
include "mpbid.mm"

theorem dihjat5N
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
  assume dihjat5.b: |- B = ( Base ` K )
  assume dihjat5.h: |- H = ( LHyp ` K )
  assume dihjat5.j: |- .\/ = ( join ` K )
  assume dihjat5.a: |- A = ( Atoms ` K )
  assume dihjat5.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjat5.s: |- .(+) = ( LSSum ` U )
  assume dihjat5.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjat5.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjat5.x: |- ( ph -> X e. B )
  assume dihjat5.p: |- ( ph -> P e. A )


  assert |- ( ph -> ( X .\/ P ) = ( `' I ` ( ( I ` X ) .(+) ( I ` P ) ) ) )

  proof
    wph
    cX
    cP
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
    cP
    cI
    cfv
    #
    c.po
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
    cA
    cB
    cP
    c.po
    cU
    cH
    cI
    c.or
    cK
    cW
    cX
    dihjat5.b
    dihjat5.h
    dihjat5.j
    dihjat5.a
    dihjat5.u
    dihjat5.s
    dihjat5.i
    dihjat5.k
    dihjat5.x
    dihjat5.p
    dihjat3
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
    cI
    crn
    #
    wcel
    #
    @6
    @4
    wceq
    dihjat5.k
    wph
    cU
    clsa
    cfv
    #
    c.po
    @3
    cU
    cH
    cI
    cK
    cW
    @2
    dihjat5.h
    dihjat5.i
    dihjat5.u
    dihjat5.s
    @14
    eqid
    #
    dihjat5.k
    wph
    @11
    cX
    cB
    wcel
    #
    @2
    @12
    wcel
    dihjat5.k
    dihjat5.x
    cB
    cH
    cI
    cK
    cW
    cX
    dihjat5.b
    dihjat5.h
    dihjat5.i
    dihcl
    syl2anc
    wph
    @11
    cP
    cA
    wcel
    #
    @3
    @14
    wcel
    dihjat5.k
    dihjat5.p
    cA
    cP
    cU
    cH
    cI
    cK
    @14
    cW
    dihjat5.a
    dihjat5.h
    dihjat5.u
    dihjat5.i
    @15
    dihatlat
    syl2anc
    dihsmatrn
    #
    cH
    cI
    cK
    cW
    @4
    dihjat5.h
    dihjat5.i
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
    dihjat5.k
    wph
    cK
    clat
    wcel
    #
    @16
    cP
    cB
    wcel
    #
    @19
    wph
    @9
    @21
    wph
    @9
    @10
    dihjat5.k
    simpld
    cK
    hllat
    syl
    dihjat5.x
    wph
    @17
    @22
    dihjat5.p
    cA
    cB
    cP
    cK
    dihjat5.b
    dihjat5.a
    atbase
    syl
    cB
    c.or
    cK
    cX
    cP
    dihjat5.b
    dihjat5.j
    latjcl
    syl3anc
    wph
    @11
    @13
    @20
    dihjat5.k
    @18
    cB
    cH
    cI
    cK
    cW
    @4
    dihjat5.b
    dihjat5.h
    dihjat5.i
    dihcnvcl
    syl2anc
    cB
    cH
    cI
    cK
    cW
    @0
    @5
    dihjat5.b
    dihjat5.h
    dihjat5.i
    dih11
    syl3anc
    mpbid
end
