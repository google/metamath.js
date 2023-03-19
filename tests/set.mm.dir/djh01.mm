include "csn.mm"
include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "cjn.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "dih0rn.mm"
include "syl.mm"
include "djhjlj.mm"
include "cp0.mm"
include "wceq.mm"
include "dih0cnv.mm"
include "oveq2d.mm"
include "col.mm"
include "cbs.mm"
include "simpld.mm"
include "hlol.mm"
include "dihcnvcl.mm"
include "syl2anc.mm"
include "olj01.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "dihcnvid2.mm"
include "3eqtrd.mm"

theorem djh01
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume djh01.h: |- H = ( LHyp ` K )
  assume djh01.u: |- U = ( ( DVecH ` K ) ` W )
  assume djh01.o: |- .0. = ( 0g ` U )
  assume djh01.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djh01.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djh01.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djh01.x: |- ( ph -> X e. ran I )


  assert |- ( ph -> ( X .\/ { .0. } ) = X )

  proof
    wph
    cX
    c.0
    csn
    #
    c.or
    co
    cX
    cI
    ccnv
    #
    cfv
    #
    @0
    @1
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cI
    cfv
    @2
    cI
    cfv
    #
    cX
    wph
    cH
    cI
    c.or
    @4
    cK
    cW
    cX
    @0
    @4
    eqid
    #
    djh01.h
    djh01.i
    djh01.j
    djh01.k
    djh01.x
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
    @0
    cI
    crn
    #
    wcel
    djh01.k
    cU
    cH
    cI
    cK
    cW
    c.0
    djh01.h
    djh01.i
    djh01.u
    djh01.o
    dih0rn
    syl
    djhjlj
    wph
    @5
    @2
    cI
    wph
    @5
    @2
    cK
    cp0
    cfv
    #
    @4
    co
    #
    @2
    wph
    @3
    @12
    @2
    @4
    wph
    @10
    @3
    @12
    wceq
    djh01.k
    cU
    cH
    cI
    cK
    cW
    @12
    c.0
    djh01.h
    @12
    eqid
    #
    djh01.i
    djh01.u
    djh01.o
    dih0cnv
    syl
    oveq2d
    wph
    cK
    col
    wcel
    #
    @2
    cK
    cbs
    cfv
    #
    wcel
    #
    @13
    @2
    wceq
    wph
    @8
    @15
    wph
    @8
    @9
    djh01.k
    simpld
    cK
    hlol
    syl
    wph
    @10
    cX
    @11
    wcel
    #
    @17
    djh01.k
    djh01.x
    @16
    cH
    cI
    cK
    cW
    cX
    @16
    eqid
    #
    djh01.h
    djh01.i
    dihcnvcl
    syl2anc
    @16
    @4
    cK
    @2
    @12
    @19
    @7
    @14
    olj01
    syl2anc
    eqtrd
    fveq2d
    wph
    @10
    @18
    @6
    cX
    wceq
    djh01.k
    djh01.x
    cH
    cI
    cK
    cW
    cX
    djh01.h
    djh01.i
    dihcnvid2
    syl2anc
    3eqtrd
end
