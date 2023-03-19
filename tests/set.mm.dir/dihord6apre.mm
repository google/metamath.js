include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "wne.mm"
include "tendo1ne0.mm"
include "3ad2ant1.mm"
include "neneqd.mm"
include "cv.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "wrex.mm"
include "wi.mm"
include "eqid.mm"
include "lhpmcvr2.mm"
include "3adant3.mm"
include "cdic.mm"
include "cdib.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "dihvalcq.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "dihvalb.mm"
include "syl2anc.mm"
include "sseq12d.mm"
include "csubg.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsssssubg.mm"
include "syl.mm"
include "simprl.mm"
include "diclss.mm"
include "sseldd.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "simpl2l.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latmle2.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmub1.mm"
include "sstr.mm"
include "cop.mm"
include "eqidd.mm"
include "tendoidcl.mm"
include "wb.mm"
include "fvex.mm"
include "cvv.mm"
include "cltrn.mm"
include "eqeltri.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "dicopelval2.mm"
include "mpbir2and.mm"
include "ssel2.mm"
include "cdia.mm"
include "dibopelval2.mm"
include "syl6bi.mm"
include "syl5.mm"
include "mpan2d.mm"
include "mpand.mm"
include "sylbid.mm"
include "exp44.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "mtod.mm"
include "pm2.21d.mm"
include "imp.mm"

theorem dihord6apre
  let cA: class A
  let cB: class B
  let cP: class P
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vq: setvar q
  assume dihord6apre.b: |- B = ( Base ` K )
  assume dihord6apre.l: |- .<_ = ( le ` K )
  assume dihord6apre.a: |- A = ( Atoms ` K )
  assume dihord6apre.h: |- H = ( LHyp ` K )
  assume dihord6apre.p: |- P = ( ( oc ` K ) ` W )
  assume dihord6apre.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dihord6apre.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihord6apre.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihord6apre.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihord6apre.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihord6apre.s: |- .(+) = ( LSSum ` U )
  assume dihord6apre.g: |- G = ( iota_ h e. T ( h ` P ) = q )

  disjoint .<_ q
  disjoint A q
  disjoint h q
  disjoint B h
  disjoint B q
  disjoint H q
  disjoint I q
  disjoint K h
  disjoint K q
  disjoint O q
  disjoint T h
  disjoint T q
  disjoint W h
  disjoint W q
  disjoint X q
  disjoint Y q
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) /\ ( I ` X ) C_ ( I ` Y ) ) -> X .<_ Y )

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
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cY
    cB
    wcel
    cY
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    wss
    #
    cX
    cY
    c.le
    wbr
    #
    @7
    @10
    @11
    @7
    @10
    cid
    cT
    cres
    #
    cO
    wceq
    #
    @7
    @12
    cO
    @2
    @5
    @12
    cO
    wne
    @6
    cB
    cT
    vh
    cE
    cH
    cK
    cO
    cW
    dihord6apre.b
    dihord6apre.h
    dihord6apre.t
    dihord6apre.e
    dihord6apre.o
    tendo1ne0
    3ad2ant1
    neneqd
    @7
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @14
    cX
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    cX
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    @10
    @13
    wi
    #
    @2
    @5
    @21
    @6
    cA
    cB
    cH
    @18
    cK
    c.le
    @16
    cW
    cX
    vq
    dihord6apre.b
    dihord6apre.l
    @18
    eqid
    #
    @16
    eqid
    #
    dihord6apre.a
    dihord6apre.h
    lhpmcvr2
    3adant3
    @7
    @20
    @22
    vq
    cA
    @7
    @14
    cA
    wcel
    #
    @15
    @19
    @22
    @7
    @25
    @15
    @19
    @22
    @7
    @25
    @15
    wa
    #
    @19
    wa
    #
    wa
    #
    @10
    @14
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    #
    @17
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    c.po
    co
    #
    cY
    @31
    cfv
    #
    wss
    #
    @13
    @28
    @8
    @33
    @9
    @34
    @28
    @2
    @5
    @27
    @8
    @33
    wceq
    @2
    @5
    @6
    @27
    simpl1
    #
    @2
    @5
    @6
    @27
    simpl2
    @7
    @27
    simpr
    cA
    cB
    @29
    @31
    c.po
    @14
    cU
    cH
    cI
    @18
    cK
    c.le
    @16
    cW
    cX
    dihord6apre.b
    dihord6apre.l
    @23
    @24
    dihord6apre.a
    dihord6apre.h
    dihord6apre.i
    @31
    eqid
    #
    @29
    eqid
    #
    dihord6apre.u
    dihord6apre.s
    dihvalcq
    syl3anc
    @28
    @2
    @6
    @9
    @34
    wceq
    @36
    @2
    @5
    @6
    @27
    simpl3
    #
    cB
    @31
    cH
    cI
    cK
    c.le
    chlt
    cW
    cY
    dihord6apre.b
    dihord6apre.l
    dihord6apre.h
    dihord6apre.i
    @37
    dihvalb
    syl2anc
    sseq12d
    @28
    @30
    @33
    wss
    #
    @35
    @13
    @28
    @30
    cU
    csubg
    cfv
    #
    wcel
    @32
    @41
    wcel
    @40
    @28
    cU
    clss
    cfv
    #
    @41
    @30
    @28
    cU
    clmod
    wcel
    @42
    @41
    wss
    @28
    cU
    cH
    cK
    cW
    dihord6apre.h
    dihord6apre.u
    @36
    dvhlmod
    @42
    cU
    @42
    eqid
    #
    lsssssubg
    syl
    #
    @28
    @2
    @26
    @30
    @42
    wcel
    @36
    @7
    @26
    @19
    simprl
    #
    cA
    @14
    @42
    cU
    cH
    @29
    cK
    c.le
    cW
    dihord6apre.l
    dihord6apre.a
    dihord6apre.h
    dihord6apre.u
    @38
    @43
    diclss
    syl2anc
    sseldd
    @28
    @42
    @41
    @32
    @44
    @28
    @2
    @17
    cB
    wcel
    #
    @17
    cW
    c.le
    wbr
    #
    @32
    @42
    wcel
    @36
    @28
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @46
    @28
    @0
    @48
    @0
    @1
    @5
    @6
    @27
    simpl1l
    cK
    hllat
    syl
    #
    @3
    @4
    @2
    @6
    @27
    simpl2l
    #
    @28
    @1
    @49
    @0
    @1
    @5
    @6
    @27
    simpl1r
    cB
    cH
    cK
    cW
    dihord6apre.b
    dihord6apre.h
    lhpbase
    syl
    #
    cB
    cK
    @16
    cX
    cW
    dihord6apre.b
    @24
    latmcl
    syl3anc
    @28
    @48
    @3
    @49
    @47
    @50
    @51
    @52
    cB
    cK
    c.le
    @16
    cX
    cW
    dihord6apre.b
    dihord6apre.l
    @24
    latmle2
    syl3anc
    cB
    @42
    cU
    cH
    @31
    cK
    c.le
    cW
    @17
    dihord6apre.b
    dihord6apre.l
    dihord6apre.h
    dihord6apre.u
    @37
    @43
    diblss
    syl12anc
    sseldd
    c.po
    @30
    @32
    cU
    dihord6apre.s
    lsmub1
    syl2anc
    @40
    @35
    wa
    @30
    @34
    wss
    #
    @28
    @13
    @30
    @33
    @34
    sstr
    @28
    @53
    cG
    @12
    cfv
    #
    @12
    cop
    #
    @30
    wcel
    #
    @13
    @28
    @56
    @54
    @54
    wceq
    #
    @12
    cE
    wcel
    #
    @28
    @54
    eqidd
    @28
    @2
    @58
    @36
    cT
    cE
    cH
    cK
    cW
    dihord6apre.h
    dihord6apre.t
    dihord6apre.e
    tendoidcl
    syl
    @28
    @2
    @26
    @56
    @57
    @58
    wa
    wb
    @36
    @45
    cA
    cP
    @14
    @12
    cT
    vh
    cE
    @54
    cG
    cH
    @29
    cK
    c.le
    chlt
    cW
    dihord6apre.l
    dihord6apre.a
    dihord6apre.h
    dihord6apre.p
    dihord6apre.t
    dihord6apre.e
    @38
    dihord6apre.g
    cG
    @12
    fvex
    cT
    cvv
    wcel
    @12
    cvv
    wcel
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dihord6apre.t
    cW
    @59
    fvex
    eqeltri
    cT
    cvv
    resiexg
    ax-mp
    dicopelval2
    syl2anc
    mpbir2and
    @53
    @56
    wa
    @55
    @34
    wcel
    #
    @28
    @13
    @30
    @34
    @55
    ssel2
    @28
    @60
    @54
    cY
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    wcel
    #
    @13
    wa
    #
    @13
    @28
    @2
    @6
    @60
    @63
    wb
    @36
    @39
    cB
    @12
    cT
    vh
    @54
    cH
    @31
    @61
    cK
    c.le
    chlt
    cW
    cY
    cO
    dihord6apre.b
    dihord6apre.l
    dihord6apre.h
    dihord6apre.t
    dihord6apre.o
    @61
    eqid
    @37
    dibopelval2
    syl2anc
    @62
    @13
    simpr
    syl6bi
    syl5
    mpan2d
    syl5
    mpand
    sylbid
    exp44
    imp4a
    rexlimdv
    mpd
    mtod
    pm2.21d
    imp
end
