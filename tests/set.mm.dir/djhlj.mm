include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "coch.mm"
include "cin.mm"
include "coc.mm"
include "cmee.mm"
include "cdvh.mm"
include "cbs.mm"
include "wss.mm"
include "wceq.mm"
include "simpl.mm"
include "simprl.mm"
include "eqid.mm"
include "dihss.mm"
include "syldan.mm"
include "simprr.mm"
include "djhval.mm"
include "syl12anc.mm"
include "cops.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "dihmeet.mm"
include "syl3anc.mm"
include "dochvalr2.mm"
include "ineq12d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "eqtr3d.mm"
include "col.mm"
include "hlol.mm"
include "oldmm4.mm"
include "3eqtrrd.mm"

theorem djhlj
  let cB: class B
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhlj.b: |- B = ( Base ` K )
  assume djhlj.k: |- .\/ = ( join ` K )
  assume djhlj.h: |- H = ( LHyp ` K )
  assume djhlj.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djhlj.j: |- J = ( ( joinH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ Y e. B ) ) -> ( I ` ( X .\/ Y ) ) = ( ( I ` X ) J ( I ` Y ) ) )

  proof
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
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cJ
    co
    #
    @7
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    @8
    @10
    cfv
    #
    cin
    #
    @10
    cfv
    #
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    cY
    @15
    cfv
    #
    cK
    cmee
    cfv
    #
    co
    #
    @15
    cfv
    #
    cI
    cfv
    #
    cX
    cY
    c.or
    co
    #
    cI
    cfv
    @6
    @2
    @7
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
    @8
    @24
    wss
    #
    @9
    @14
    wceq
    @2
    @5
    simpl
    #
    @2
    @5
    @3
    @25
    @2
    @3
    @4
    simprl
    #
    cB
    @23
    cH
    cI
    cK
    @24
    cW
    cX
    djhlj.b
    djhlj.h
    djhlj.i
    @23
    eqid
    #
    @24
    eqid
    #
    dihss
    syldan
    @2
    @5
    @4
    @26
    @2
    @3
    @4
    simprr
    #
    cB
    @23
    cH
    cI
    cK
    @24
    cW
    cY
    djhlj.b
    djhlj.h
    djhlj.i
    @29
    @30
    dihss
    syldan
    @23
    cH
    cJ
    cK
    @10
    @24
    cW
    @7
    @8
    djhlj.h
    @29
    @30
    @10
    eqid
    #
    djhlj.j
    djhval
    syl12anc
    @6
    @19
    cI
    cfv
    #
    @10
    cfv
    #
    @14
    @21
    @6
    @33
    @13
    @10
    @6
    @33
    @16
    cI
    cfv
    #
    @17
    cI
    cfv
    #
    cin
    #
    @13
    @6
    @2
    @16
    cB
    wcel
    #
    @17
    cB
    wcel
    #
    @33
    @37
    wceq
    @27
    @6
    cK
    cops
    wcel
    #
    @3
    @38
    @0
    @40
    @1
    @5
    cK
    hlop
    ad2antrr
    #
    @28
    cB
    cK
    @15
    cX
    djhlj.b
    @15
    eqid
    #
    opoccl
    syl2anc
    #
    @6
    @40
    @4
    @39
    @41
    @31
    cB
    cK
    @15
    cY
    djhlj.b
    @42
    opoccl
    syl2anc
    #
    cB
    cH
    cI
    cK
    @18
    cW
    @16
    @17
    djhlj.b
    @18
    eqid
    #
    djhlj.h
    djhlj.i
    dihmeet
    syl3anc
    @6
    @11
    @35
    @12
    @36
    @2
    @5
    @3
    @11
    @35
    wceq
    @28
    cB
    cH
    cI
    cK
    @10
    @15
    cW
    cX
    djhlj.b
    @42
    djhlj.h
    djhlj.i
    @32
    dochvalr2
    syldan
    @2
    @5
    @4
    @12
    @36
    wceq
    @31
    cB
    cH
    cI
    cK
    @10
    @15
    cW
    cY
    djhlj.b
    @42
    djhlj.h
    djhlj.i
    @32
    dochvalr2
    syldan
    ineq12d
    eqtr4d
    fveq2d
    @2
    @5
    @19
    cB
    wcel
    #
    @34
    @21
    wceq
    @6
    cK
    clat
    wcel
    #
    @38
    @39
    @46
    @0
    @47
    @1
    @5
    cK
    hllat
    ad2antrr
    @43
    @44
    cB
    cK
    @18
    @16
    @17
    djhlj.b
    @45
    latmcl
    syl3anc
    cB
    cH
    cI
    cK
    @10
    @15
    cW
    @19
    djhlj.b
    @42
    djhlj.h
    djhlj.i
    @32
    dochvalr2
    syldan
    eqtr3d
    @6
    @20
    @22
    cI
    @6
    cK
    col
    wcel
    #
    @3
    @4
    @20
    @22
    wceq
    @0
    @48
    @1
    @5
    cK
    hlol
    ad2antrr
    @28
    @31
    cB
    c.or
    cK
    @18
    @15
    cX
    cY
    djhlj.b
    djhlj.k
    @45
    @42
    oldmm4
    syl3anc
    fveq2d
    3eqtrrd
end
