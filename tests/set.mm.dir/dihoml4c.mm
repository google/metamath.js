include "cfv.mm"
include "cin.mm"
include "ccnv.mm"
include "wceq.mm"
include "cmee.mm"
include "co.mm"
include "coc.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdvh.mm"
include "cbs.mm"
include "wss.mm"
include "crn.mm"
include "inss1.mm"
include "dihrnss.mm"
include "syl2anc.mm"
include "dochssv.mm"
include "syl5ss.mm"
include "dochcl.mm"
include "dihmeet2.mm"
include "dihmeetcl.mm"
include "syl12anc.mm"
include "dochvalr3.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "cple.mm"
include "wbr.mm"
include "dihcnvord.mm"
include "mpbird.mm"
include "coml.mm"
include "wi.mm"
include "simpld.mm"
include "hloml.mm"
include "syl.mm"
include "dihcnvcl.mm"
include "omllaw4.mm"
include "syl3anc.mm"
include "mpd.mm"
include "3eqtrd.mm"
include "dihcnv11.mm"
include "mpbid.mm"

theorem dihoml4c
  let wph: wff ph
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihoml4c.h: |- H = ( LHyp ` K )
  assume dihoml4c.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihoml4c.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dihoml4c.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihoml4c.x: |- ( ph -> X e. ran I )
  assume dihoml4c.y: |- ( ph -> Y e. ran I )
  assume dihoml4c.l: |- ( ph -> X C_ Y )


  assert |- ( ph -> ( ( ._|_ ` ( ( ._|_ ` X ) i^i Y ) ) i^i Y ) = X )

  proof
    wph
    cX
    c.pe
    cfv
    #
    cY
    cin
    #
    c.pe
    cfv
    #
    cY
    cin
    #
    cI
    ccnv
    #
    cfv
    #
    cX
    @4
    cfv
    #
    wceq
    @3
    cX
    wceq
    wph
    @5
    @2
    @4
    cfv
    #
    cY
    @4
    cfv
    #
    cK
    cmee
    cfv
    #
    co
    @6
    cK
    coc
    cfv
    #
    cfv
    #
    @8
    @9
    co
    #
    @10
    cfv
    #
    @8
    @9
    co
    #
    @6
    wph
    cH
    cI
    cK
    @9
    cW
    @2
    cY
    @9
    eqid
    #
    dihoml4c.h
    dihoml4c.i
    dihoml4c.k
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
    @1
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
    @2
    cI
    crn
    #
    wcel
    #
    dihoml4c.k
    wph
    @1
    @0
    @20
    @0
    cY
    inss1
    wph
    @18
    cX
    @20
    wss
    #
    @0
    @20
    wss
    dihoml4c.k
    wph
    @18
    cX
    @21
    wcel
    #
    @23
    dihoml4c.k
    dihoml4c.x
    @19
    cH
    cI
    cK
    @20
    cW
    cX
    dihoml4c.h
    @19
    eqid
    #
    dihoml4c.i
    @20
    eqid
    #
    dihrnss
    syl2anc
    #
    @19
    cH
    cK
    c.pe
    @20
    cW
    cX
    dihoml4c.h
    @25
    @26
    dihoml4c.o
    dochssv
    syl2anc
    syl5ss
    @19
    cH
    cI
    cK
    c.pe
    @20
    cW
    @1
    dihoml4c.h
    dihoml4c.i
    @25
    @26
    dihoml4c.o
    dochcl
    syl2anc
    #
    dihoml4c.y
    dihmeet2
    wph
    @7
    @13
    @8
    @9
    wph
    @1
    @4
    cfv
    #
    @10
    cfv
    @7
    @13
    wph
    cH
    cI
    cK
    c.pe
    @10
    cW
    @1
    @10
    eqid
    #
    dihoml4c.h
    dihoml4c.i
    dihoml4c.o
    dihoml4c.k
    wph
    @18
    @0
    @21
    wcel
    #
    cY
    @21
    wcel
    #
    @1
    @21
    wcel
    dihoml4c.k
    wph
    @18
    @23
    @31
    dihoml4c.k
    @27
    @19
    cH
    cI
    cK
    c.pe
    @20
    cW
    cX
    dihoml4c.h
    dihoml4c.i
    @25
    @26
    dihoml4c.o
    dochcl
    syl2anc
    #
    dihoml4c.y
    cH
    cI
    cK
    cW
    @0
    cY
    dihoml4c.h
    dihoml4c.i
    dihmeetcl
    syl12anc
    dochvalr3
    wph
    @29
    @12
    @10
    wph
    @29
    @0
    @4
    cfv
    #
    @8
    @9
    co
    @12
    wph
    cH
    cI
    cK
    @9
    cW
    @0
    cY
    @15
    dihoml4c.h
    dihoml4c.i
    dihoml4c.k
    @33
    dihoml4c.y
    dihmeet2
    wph
    @11
    @34
    @8
    @9
    wph
    cH
    cI
    cK
    c.pe
    @10
    cW
    cX
    @30
    dihoml4c.h
    dihoml4c.i
    dihoml4c.o
    dihoml4c.k
    dihoml4c.x
    dochvalr3
    oveq1d
    eqtr4d
    fveq2d
    eqtr3d
    oveq1d
    wph
    @6
    @8
    cK
    cple
    cfv
    #
    wbr
    #
    @14
    @6
    wceq
    #
    wph
    @36
    cX
    cY
    wss
    dihoml4c.l
    wph
    cH
    cI
    cK
    @35
    cW
    cX
    cY
    @35
    eqid
    #
    dihoml4c.h
    dihoml4c.i
    dihoml4c.k
    dihoml4c.x
    dihoml4c.y
    dihcnvord
    mpbird
    wph
    cK
    coml
    wcel
    #
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @8
    @40
    wcel
    #
    @36
    @37
    wi
    wph
    @16
    @39
    wph
    @16
    @17
    dihoml4c.k
    simpld
    cK
    hloml
    syl
    wph
    @18
    @24
    @41
    dihoml4c.k
    dihoml4c.x
    @40
    cH
    cI
    cK
    cW
    cX
    @40
    eqid
    #
    dihoml4c.h
    dihoml4c.i
    dihcnvcl
    syl2anc
    wph
    @18
    @32
    @42
    dihoml4c.k
    dihoml4c.y
    @40
    cH
    cI
    cK
    cW
    cY
    @43
    dihoml4c.h
    dihoml4c.i
    dihcnvcl
    syl2anc
    @40
    cK
    @35
    @9
    @10
    @6
    @8
    @43
    @38
    @15
    @30
    omllaw4
    syl3anc
    mpd
    3eqtrd
    wph
    cH
    cI
    cK
    cW
    @3
    cX
    dihoml4c.h
    dihoml4c.i
    dihoml4c.k
    wph
    @18
    @22
    @32
    @3
    @21
    wcel
    dihoml4c.k
    @28
    dihoml4c.y
    cH
    cI
    cK
    cW
    @2
    cY
    dihoml4c.h
    dihoml4c.i
    dihmeetcl
    syl12anc
    dihoml4c.x
    dihcnv11
    mpbid
end
