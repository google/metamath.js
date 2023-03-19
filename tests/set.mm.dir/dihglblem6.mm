include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "cv.mm"
include "ciin.mm"
include "wceq.mm"
include "cmee.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "cdib.mm"
include "eqid.mm"
include "dihglblem4.mm"
include "wpss.mm"
include "wn.mm"
include "wi.mm"
include "wfal.mm"
include "fal.mm"
include "simpll.mm"
include "dvhlmod.mm"
include "ccla.mm"
include "simplll.mm"
include "hlclat.mm"
include "syl.mm"
include "simplrl.mm"
include "clatglbcl.mm"
include "syl2anc.mm"
include "dihlss.mm"
include "dihglblem5.mm"
include "adantr.mm"
include "simpr.mm"
include "lpssat.mm"
include "ex.mm"
include "w3a.mm"
include "ccnv.mm"
include "crn.mm"
include "simp1l.mm"
include "dih1dimat.mm"
include "adantlr.mm"
include "3adant3.mm"
include "dihcnvid2.mm"
include "wbr.mm"
include "wral.mm"
include "simp3l.mm"
include "ssiin.mm"
include "sylib.mm"
include "wb.mm"
include "wf1o.mm"
include "wf1.mm"
include "dihf11.mm"
include "f1f1orn.mm"
include "3syl.mm"
include "f1ocnvdm.mm"
include "sselda.mm"
include "dihord.mm"
include "syl3anc.mm"
include "sseq1d.mm"
include "bitr3d.mm"
include "ralbidva.mm"
include "mpbird.mm"
include "simp1ll.mm"
include "simp1rl.mm"
include "clatleglb.mm"
include "eqsstr3d.mm"
include "simp3r.mm"
include "pm2.21fal.mm"
include "rexlimdv3a.mm"
include "syld.mm"
include "mtoi.mm"
include "dfpss3.mm"
include "notbii.mm"
include "iman.mm"
include "anclb.mm"
include "3bitr2i.mm"
include "mpd.mm"
include "eqss.mm"
include "sylibr.mm"

theorem dihglblem6
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vu: setvar u
  let vv: setvar v
  let vp: setvar p
  assume dihglblem6.b: |- B = ( Base ` K )
  assume dihglblem6.l: |- .<_ = ( le ` K )
  assume dihglblem6.m: |- ./\ = ( meet ` K )
  assume dihglblem6.a: |- A = ( Atoms ` K )
  assume dihglblem6.g: |- G = ( glb ` K )
  assume dihglblem6.h: |- H = ( LHyp ` K )
  assume dihglblem6.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihglblem6.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihglblem6.s: |- P = ( LSubSp ` U )
  assume dihglblem6.d: |- D = ( LSAtoms ` U )

  disjoint ./\ x
  disjoint .<_ x
  disjoint B x
  disjoint D x
  disjoint G x
  disjoint H x
  disjoint I x
  disjoint K x
  disjoint P x
  disjoint S x
  disjoint W x
  disjoint u v
  disjoint u x
  disjoint ./\ u
  disjoint v x
  disjoint ./\ v
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint .<_ p
  disjoint .<_ u
  disjoint .<_ v
  disjoint B p
  disjoint B u
  disjoint B v
  disjoint D p
  disjoint G p
  disjoint G u
  disjoint G v
  disjoint H p
  disjoint H u
  disjoint H v
  disjoint I p
  disjoint K p
  disjoint K u
  disjoint K v
  disjoint P p
  disjoint S p
  disjoint S u
  disjoint S v
  disjoint U p
  disjoint W p
  disjoint W u
  disjoint W v
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ B /\ S =/= (/) ) ) -> ( I ` ( G ` S ) ) = |^|_ x e. S ( I ` x ) )

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
    cS
    cB
    wss
    #
    cS
    c0
    wne
    #
    wa
    #
    wa
    #
    cS
    cG
    cfv
    #
    cI
    cfv
    #
    vx
    cS
    vx
    cv
    #
    cI
    cfv
    #
    ciin
    #
    wss
    #
    @11
    @8
    wss
    #
    wa
    #
    @8
    @11
    wceq
    @6
    @12
    @14
    vx
    vv
    vu
    cB
    cS
    vu
    cv
    vv
    cv
    cW
    cK
    cmee
    cfv
    #
    co
    wceq
    vv
    cS
    wrex
    vu
    cB
    crab
    #
    cG
    cH
    cI
    cW
    cK
    cdib
    cfv
    cfv
    #
    cK
    c.le
    @15
    cW
    dihglblem6.b
    dihglblem6.l
    @15
    eqid
    dihglblem6.g
    dihglblem6.h
    @16
    eqid
    @17
    eqid
    dihglblem6.i
    dihglblem4
    @6
    @8
    @11
    wpss
    #
    wn
    #
    @12
    @14
    wi
    #
    @6
    @18
    wfal
    fal
    @6
    @18
    vp
    cv
    #
    @11
    wss
    #
    @21
    @8
    wss
    #
    wn
    #
    wa
    #
    vp
    cD
    wrex
    #
    wfal
    @6
    @18
    @26
    @6
    @18
    wa
    #
    cD
    cP
    @8
    @11
    cU
    vp
    dihglblem6.s
    dihglblem6.d
    @27
    cU
    cH
    cK
    cW
    dihglblem6.h
    dihglblem6.u
    @2
    @5
    @18
    simpll
    #
    dvhlmod
    @27
    @2
    @7
    cB
    wcel
    #
    @8
    cP
    wcel
    @28
    @27
    cK
    ccla
    wcel
    #
    @3
    @29
    @27
    @0
    @30
    @0
    @1
    @5
    @18
    simplll
    cK
    hlclat
    #
    syl
    @2
    @3
    @4
    @18
    simplrl
    cB
    cS
    cG
    cK
    dihglblem6.b
    dihglblem6.g
    clatglbcl
    #
    syl2anc
    cB
    cP
    cU
    cH
    cI
    cK
    cW
    @7
    dihglblem6.b
    dihglblem6.h
    dihglblem6.i
    dihglblem6.u
    dihglblem6.s
    dihlss
    syl2anc
    @6
    @11
    cP
    wcel
    @18
    vx
    cB
    cP
    cS
    cU
    cG
    cH
    cI
    cK
    cW
    dihglblem6.b
    dihglblem6.g
    dihglblem6.h
    dihglblem6.u
    dihglblem6.i
    dihglblem6.s
    dihglblem5
    adantr
    @6
    @18
    simpr
    lpssat
    ex
    @6
    @25
    wfal
    vp
    cD
    @6
    @21
    cD
    wcel
    #
    @25
    w3a
    #
    @23
    @34
    @21
    @21
    cI
    ccnv
    cfv
    #
    cI
    cfv
    #
    @8
    @34
    @2
    @21
    cI
    crn
    #
    wcel
    #
    @36
    @21
    wceq
    #
    @2
    @5
    @33
    @25
    simp1l
    #
    @6
    @33
    @38
    @25
    @2
    @33
    @38
    @5
    cD
    @21
    cU
    cH
    cI
    cK
    cW
    dihglblem6.h
    dihglblem6.u
    dihglblem6.i
    dihglblem6.d
    dih1dimat
    adantlr
    #
    3adant3
    cH
    cI
    cK
    cW
    @21
    dihglblem6.h
    dihglblem6.i
    dihcnvid2
    #
    syl2anc
    @34
    @36
    @8
    wss
    #
    @35
    @7
    c.le
    wbr
    #
    @34
    @44
    @35
    @9
    c.le
    wbr
    #
    vx
    cS
    wral
    #
    @34
    @46
    @21
    @10
    wss
    #
    vx
    cS
    wral
    #
    @34
    @22
    @48
    @6
    @33
    @22
    @24
    simp3l
    vx
    cS
    @10
    @21
    ssiin
    sylib
    @6
    @33
    @46
    @48
    wb
    @25
    @6
    @33
    wa
    #
    @45
    @47
    vx
    cS
    @49
    @9
    cS
    wcel
    #
    wa
    #
    @36
    @10
    wss
    #
    @45
    @47
    @51
    @2
    @35
    cB
    wcel
    #
    @9
    cB
    wcel
    @52
    @45
    wb
    @2
    @5
    @33
    @50
    simplll
    @49
    @53
    @50
    @49
    cB
    @37
    cI
    wf1o
    #
    @38
    @53
    @49
    @2
    cB
    cP
    cI
    wf1
    @54
    @2
    @5
    @33
    simpll
    #
    cB
    cP
    cU
    cH
    cI
    cK
    cW
    dihglblem6.b
    dihglblem6.h
    dihglblem6.i
    dihglblem6.u
    dihglblem6.s
    dihf11
    cB
    cP
    cI
    f1f1orn
    3syl
    @41
    cB
    @37
    @21
    cI
    f1ocnvdm
    syl2anc
    #
    adantr
    @49
    cS
    cB
    @9
    @2
    @3
    @4
    @33
    simplrl
    sselda
    cB
    cH
    cI
    cK
    c.le
    cW
    @35
    @9
    dihglblem6.b
    dihglblem6.l
    dihglblem6.h
    dihglblem6.i
    dihord
    syl3anc
    @51
    @36
    @21
    @10
    @49
    @39
    @50
    @49
    @2
    @38
    @39
    @55
    @41
    @42
    syl2anc
    adantr
    sseq1d
    bitr3d
    ralbidva
    3adant3
    mpbird
    @34
    @30
    @53
    @3
    @44
    @46
    wb
    @34
    @0
    @30
    @0
    @1
    @5
    @33
    @25
    simp1ll
    @31
    syl
    #
    @6
    @33
    @53
    @25
    @56
    3adant3
    #
    @3
    @4
    @2
    @33
    @25
    simp1rl
    #
    vx
    cB
    cS
    cG
    cK
    c.le
    @35
    dihglblem6.b
    dihglblem6.l
    dihglblem6.g
    clatleglb
    syl3anc
    mpbird
    @34
    @2
    @53
    @29
    @43
    @44
    wb
    @40
    @58
    @34
    @30
    @3
    @29
    @57
    @59
    @32
    syl2anc
    cB
    cH
    cI
    cK
    c.le
    cW
    @35
    @7
    dihglblem6.b
    dihglblem6.l
    dihglblem6.h
    dihglblem6.i
    dihord
    syl3anc
    mpbird
    eqsstr3d
    @6
    @33
    @22
    @24
    simp3r
    pm2.21fal
    rexlimdv3a
    syld
    mtoi
    @19
    @12
    @13
    wn
    wa
    #
    wn
    @12
    @13
    wi
    @20
    @18
    @60
    @8
    @11
    dfpss3
    notbii
    @12
    @13
    iman
    @12
    @13
    anclb
    3bitr2i
    sylib
    mpd
    @8
    @11
    eqss
    sylibr
end
