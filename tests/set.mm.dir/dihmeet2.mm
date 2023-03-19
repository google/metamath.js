include "cin.mm"
include "ccnv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "dihcnvid2.mm"
include "syl2anc.mm"
include "ineq12d.mm"
include "cbs.mm"
include "eqid.mm"
include "dihcnvcl.mm"
include "dihmeet.mm"
include "syl3anc.mm"
include "dihmeetcl.mm"
include "syl12anc.mm"
include "3eqtr4rd.mm"
include "wb.mm"
include "clat.mm"
include "simpld.mm"
include "hllat.mm"
include "syl.mm"
include "latmcl.mm"
include "dih11.mm"
include "mpbid.mm"

theorem dihmeet2
  let wph: wff ph
  let cH: class H
  let cI: class I
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihmeet2.m: |- ./\ = ( meet ` K )
  assume dihmeet2.h: |- H = ( LHyp ` K )
  assume dihmeet2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihmeet2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihmeet2.x: |- ( ph -> X e. ran I )
  assume dihmeet2.y: |- ( ph -> Y e. ran I )


  assert |- ( ph -> ( `' I ` ( X i^i Y ) ) = ( ( `' I ` X ) ./\ ( `' I ` Y ) ) )

  proof
    wph
    cX
    cY
    cin
    #
    cI
    ccnv
    #
    cfv
    #
    cI
    cfv
    #
    cX
    @1
    cfv
    #
    cY
    @1
    cfv
    #
    c.an
    co
    #
    cI
    cfv
    #
    wceq
    #
    @2
    @6
    wceq
    #
    wph
    @4
    cI
    cfv
    #
    @5
    cI
    cfv
    #
    cin
    #
    @0
    @7
    @3
    wph
    @10
    cX
    @11
    cY
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
    cX
    cI
    crn
    #
    wcel
    #
    @10
    cX
    wceq
    dihmeet2.k
    dihmeet2.x
    cH
    cI
    cK
    cW
    cX
    dihmeet2.h
    dihmeet2.i
    dihcnvid2
    syl2anc
    wph
    @15
    cY
    @16
    wcel
    #
    @11
    cY
    wceq
    dihmeet2.k
    dihmeet2.y
    cH
    cI
    cK
    cW
    cY
    dihmeet2.h
    dihmeet2.i
    dihcnvid2
    syl2anc
    ineq12d
    wph
    @15
    @4
    cK
    cbs
    cfv
    #
    wcel
    #
    @5
    @19
    wcel
    #
    @7
    @12
    wceq
    dihmeet2.k
    wph
    @15
    @17
    @20
    dihmeet2.k
    dihmeet2.x
    @19
    cH
    cI
    cK
    cW
    cX
    @19
    eqid
    #
    dihmeet2.h
    dihmeet2.i
    dihcnvcl
    syl2anc
    #
    wph
    @15
    @18
    @21
    dihmeet2.k
    dihmeet2.y
    @19
    cH
    cI
    cK
    cW
    cY
    @22
    dihmeet2.h
    dihmeet2.i
    dihcnvcl
    syl2anc
    #
    @19
    cH
    cI
    cK
    c.an
    cW
    @4
    @5
    @22
    dihmeet2.m
    dihmeet2.h
    dihmeet2.i
    dihmeet
    syl3anc
    wph
    @15
    @0
    @16
    wcel
    #
    @3
    @0
    wceq
    dihmeet2.k
    wph
    @15
    @17
    @18
    @25
    dihmeet2.k
    dihmeet2.x
    dihmeet2.y
    cH
    cI
    cK
    cW
    cX
    cY
    dihmeet2.h
    dihmeet2.i
    dihmeetcl
    syl12anc
    #
    cH
    cI
    cK
    cW
    @0
    dihmeet2.h
    dihmeet2.i
    dihcnvid2
    syl2anc
    3eqtr4rd
    wph
    @15
    @2
    @19
    wcel
    #
    @6
    @19
    wcel
    #
    @8
    @9
    wb
    dihmeet2.k
    wph
    @15
    @25
    @27
    dihmeet2.k
    @26
    @19
    cH
    cI
    cK
    cW
    @0
    @22
    dihmeet2.h
    dihmeet2.i
    dihcnvcl
    syl2anc
    wph
    cK
    clat
    wcel
    #
    @20
    @21
    @28
    wph
    @13
    @29
    wph
    @13
    @14
    dihmeet2.k
    simpld
    cK
    hllat
    syl
    @23
    @24
    @19
    cK
    c.an
    @4
    @5
    @22
    dihmeet2.m
    latmcl
    syl3anc
    @19
    cH
    cI
    cK
    cW
    @2
    @6
    @22
    dihmeet2.h
    dihmeet2.i
    dih11
    syl3anc
    mpbid
end
