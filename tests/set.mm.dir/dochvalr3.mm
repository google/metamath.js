include "ccnv.mm"
include "cfv.mm"
include "wceq.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cdvh.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "dihrnss.mm"
include "syl2anc.mm"
include "dochcl.mm"
include "dihcnvid2.mm"
include "dochvalr.mm"
include "eqtr2d.mm"
include "wb.mm"
include "cops.mm"
include "simpld.mm"
include "hlop.mm"
include "syl.mm"
include "dihcnvcl.mm"
include "opoccl.mm"
include "dih11.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem dochvalr3
  let wph: wff ph
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume dochvalr3.o: |- ._|_ = ( oc ` K )
  assume dochvalr3.h: |- H = ( LHyp ` K )
  assume dochvalr3.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochvalr3.n: |- N = ( ( ocH ` K ) ` W )
  assume dochvalr3.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochvalr3.x: |- ( ph -> X e. ran I )


  assert |- ( ph -> ( ._|_ ` ( `' I ` X ) ) = ( `' I ` ( N ` X ) ) )

  proof
    wph
    cX
    cI
    ccnv
    #
    cfv
    #
    c.pe
    cfv
    #
    cI
    cfv
    #
    cX
    cN
    cfv
    #
    @0
    cfv
    #
    cI
    cfv
    #
    wceq
    #
    @2
    @5
    wceq
    #
    wph
    @6
    @4
    @3
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
    dochvalr3.k
    wph
    @11
    cX
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
    @13
    dochvalr3.k
    wph
    @11
    cX
    @12
    wcel
    #
    @16
    dochvalr3.k
    dochvalr3.x
    @14
    cH
    cI
    cK
    @15
    cW
    cX
    dochvalr3.h
    @14
    eqid
    #
    dochvalr3.i
    @15
    eqid
    #
    dihrnss
    syl2anc
    @14
    cH
    cI
    cK
    cN
    @15
    cW
    cX
    dochvalr3.h
    dochvalr3.i
    @18
    @19
    dochvalr3.n
    dochcl
    syl2anc
    #
    cH
    cI
    cK
    cW
    @4
    dochvalr3.h
    dochvalr3.i
    dihcnvid2
    syl2anc
    wph
    @11
    @17
    @4
    @3
    wceq
    dochvalr3.k
    dochvalr3.x
    cH
    cI
    cK
    cN
    c.pe
    cW
    cX
    dochvalr3.o
    dochvalr3.h
    dochvalr3.i
    dochvalr3.n
    dochvalr
    syl2anc
    eqtr2d
    wph
    @11
    @2
    cK
    cbs
    cfv
    #
    wcel
    #
    @5
    @21
    wcel
    #
    @7
    @8
    wb
    dochvalr3.k
    wph
    cK
    cops
    wcel
    #
    @1
    @21
    wcel
    #
    @22
    wph
    @9
    @24
    wph
    @9
    @10
    dochvalr3.k
    simpld
    cK
    hlop
    syl
    wph
    @11
    @17
    @25
    dochvalr3.k
    dochvalr3.x
    @21
    cH
    cI
    cK
    cW
    cX
    @21
    eqid
    #
    dochvalr3.h
    dochvalr3.i
    dihcnvcl
    syl2anc
    @21
    cK
    c.pe
    @1
    @26
    dochvalr3.o
    opoccl
    syl2anc
    wph
    @11
    @13
    @23
    dochvalr3.k
    @20
    @21
    cH
    cI
    cK
    cW
    @4
    @26
    dochvalr3.h
    dochvalr3.i
    dihcnvcl
    syl2anc
    @21
    cH
    cI
    cK
    cW
    @2
    @5
    @26
    dochvalr3.h
    dochvalr3.i
    dih11
    syl3anc
    mpbid
end
