include "wpss.mm"
include "csn.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "w3a.mm"
include "simp3.mm"
include "simp2.mm"
include "pssss.mm"
include "syl.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "pssnel.mm"
include "cplusg.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl3.mm"
include "simprl.mm"
include "sseldd.mm"
include "wb.mm"
include "csubg.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "lsssssubg.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "lsmelval.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "mpbid.mm"
include "c0g.mm"
include "wne.mm"
include "simp1rr.mm"
include "simp2l.mm"
include "wi.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "biimpac.mm"
include "ad2antrr.mm"
include "lssel.mm"
include "lmod0vrid.mm"
include "biimpd.mm"
include "ex.mm"
include "syl7.mm"
include "exp4a.mm"
include "3imp.mm"
include "eleq1.mm"
include "biimparc.mm"
include "syl6an.mm"
include "necon3bd.mm"
include "mpd.mm"
include "csg.mm"
include "cabl.mm"
include "lmodabl.mm"
include "simp1l1.mm"
include "simp2r.mm"
include "ablpncan2.mm"
include "syl3anc.mm"
include "simp1rl.mm"
include "eqeltrrd.mm"
include "simp1l2.mm"
include "sselda.mm"
include "lssvsubcl.mm"
include "syl22anc.mm"
include "simp12r.mm"
include "lspsneleq.mm"
include "lspsnel5a.mm"
include "eqsstr3d.mm"
include "mpd3an23.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "exlimddv.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "eqssd.mm"

theorem lsmcv
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lsmcv.v: |- V = ( Base ` W )
  assume lsmcv.s: |- S = ( LSubSp ` W )
  assume lsmcv.n: |- N = ( LSpan ` W )
  assume lsmcv.p: |- .(+) = ( LSSum ` W )
  assume lsmcv.w: |- ( ph -> W e. LVec )
  assume lsmcv.t: |- ( ph -> T e. S )
  assume lsmcv.u: |- ( ph -> U e. S )
  assume lsmcv.x: |- ( ph -> X e. V )


  assert |- ( ( ph /\ T C. U /\ U C_ ( T .(+) ( N ` { X } ) ) ) -> U = ( T .(+) ( N ` { X } ) ) )

  proof
    wph
    cT
    cU
    wpss
    #
    cU
    cT
    cX
    csn
    cN
    cfv
    #
    c.po
    co
    #
    wss
    #
    w3a
    #
    cU
    @2
    wph
    @0
    @3
    simp3
    @4
    cT
    cU
    wss
    #
    @1
    cU
    wss
    #
    @2
    cU
    wss
    #
    @4
    @0
    @5
    wph
    @0
    @3
    simp2
    #
    cT
    cU
    pssss
    #
    syl
    @4
    vx
    cv
    #
    cU
    wcel
    #
    @10
    cT
    wcel
    #
    wn
    #
    wa
    #
    @6
    vx
    @4
    @0
    @14
    vx
    wex
    @8
    vx
    cT
    cU
    pssnel
    syl
    @4
    @14
    wa
    #
    @10
    vy
    cv
    #
    vz
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    @1
    wrex
    vy
    cT
    wrex
    #
    @6
    @15
    @10
    @2
    wcel
    #
    @21
    @15
    cU
    @2
    @10
    wph
    @0
    @3
    @14
    simpl3
    @4
    @11
    @13
    simprl
    sseldd
    @4
    @22
    @21
    wb
    #
    @14
    wph
    @0
    @23
    @3
    wph
    cT
    cW
    csubg
    cfv
    #
    wcel
    #
    @1
    @24
    wcel
    #
    @23
    wph
    cS
    @24
    cT
    wph
    cW
    clmod
    wcel
    #
    cS
    @24
    wss
    wph
    cW
    clvec
    wcel
    #
    @27
    lsmcv.w
    cW
    lveclmod
    #
    syl
    #
    cS
    cW
    lsmcv.s
    lsssssubg
    syl
    #
    lsmcv.t
    sseldd
    #
    wph
    cS
    @24
    @1
    @31
    wph
    @27
    cX
    cV
    wcel
    #
    @1
    cS
    wcel
    #
    @30
    lsmcv.x
    cS
    cN
    cV
    cW
    cX
    lsmcv.v
    lsmcv.s
    lsmcv.n
    lspsncl
    #
    syl2anc
    sseldd
    #
    vy
    vz
    @18
    c.po
    cT
    @1
    cW
    @10
    @18
    eqid
    #
    lsmcv.p
    lsmelval
    syl2anc
    3ad2ant1
    adantr
    mpbid
    @15
    @20
    @6
    vy
    vz
    cT
    @1
    @15
    @16
    cT
    wcel
    #
    @17
    @1
    wcel
    #
    wa
    #
    @20
    @6
    @15
    @40
    @20
    w3a
    #
    @17
    cW
    c0g
    cfv
    #
    wne
    #
    @17
    cU
    wcel
    #
    @6
    @41
    @13
    @43
    @11
    @13
    @4
    @40
    @20
    simp1rr
    @41
    @12
    @17
    @42
    @41
    @38
    @17
    @42
    wceq
    #
    @10
    @16
    wceq
    #
    @12
    @15
    @38
    @39
    @20
    simp2l
    #
    @15
    @40
    @20
    @45
    @46
    wi
    @15
    @40
    @20
    @45
    @46
    @20
    @45
    wa
    @10
    @16
    @42
    @18
    co
    #
    wceq
    #
    @15
    @40
    @46
    @45
    @20
    @49
    @45
    @19
    @48
    @10
    @17
    @42
    @16
    @18
    oveq2
    eqeq2d
    biimpac
    @15
    @40
    @49
    @46
    wi
    @15
    @40
    wa
    #
    @49
    @46
    @50
    @48
    @16
    @10
    @50
    @27
    @16
    cV
    wcel
    #
    @48
    @16
    wceq
    @4
    @27
    @14
    @40
    wph
    @0
    @27
    @3
    @30
    3ad2ant1
    ad2antrr
    @50
    cT
    cS
    wcel
    #
    @38
    @51
    @4
    @52
    @14
    @40
    wph
    @0
    @52
    @3
    lsmcv.t
    3ad2ant1
    ad2antrr
    @15
    @38
    @39
    simprl
    cS
    cT
    cV
    cW
    @16
    lsmcv.v
    lsmcv.s
    lssel
    #
    syl2anc
    @18
    cV
    cW
    @16
    @42
    lsmcv.v
    @37
    @42
    eqid
    #
    lmod0vrid
    syl2anc
    eqeq2d
    biimpd
    ex
    syl7
    exp4a
    3imp
    @46
    @12
    @38
    @10
    @16
    cT
    eleq1
    biimparc
    syl6an
    necon3bd
    mpd
    @41
    @19
    @16
    cW
    csg
    cfv
    #
    co
    #
    @17
    cU
    @41
    cW
    cabl
    wcel
    #
    @51
    @17
    cV
    wcel
    #
    @56
    @17
    wceq
    @41
    @28
    @57
    @15
    @40
    @28
    @20
    @4
    @28
    @14
    wph
    @0
    @28
    @3
    lsmcv.w
    3ad2ant1
    adantr
    3ad2ant1
    #
    @28
    @27
    @57
    @29
    cW
    lmodabl
    syl
    syl
    @41
    @52
    @38
    @51
    @41
    wph
    @52
    wph
    @0
    @3
    @14
    @40
    @20
    simp1l1
    #
    lsmcv.t
    syl
    @47
    @53
    syl2anc
    @41
    @34
    @39
    @58
    @41
    @27
    @33
    @34
    @41
    @28
    @27
    @59
    @29
    syl
    #
    @41
    wph
    @33
    @60
    lsmcv.x
    syl
    @35
    syl2anc
    @15
    @38
    @39
    @20
    simp2r
    cS
    @1
    cV
    cW
    @17
    lsmcv.v
    lsmcv.s
    lssel
    syl2anc
    cV
    @18
    cW
    @55
    @16
    @17
    lsmcv.v
    @37
    @55
    eqid
    #
    ablpncan2
    syl3anc
    @41
    @27
    cU
    cS
    wcel
    #
    @19
    cU
    wcel
    @16
    cU
    wcel
    #
    @56
    cU
    wcel
    @61
    @41
    wph
    @63
    @60
    lsmcv.u
    syl
    @41
    @10
    @19
    cU
    @15
    @40
    @20
    simp3
    @11
    @13
    @4
    @40
    @20
    simp1rl
    eqeltrrd
    @41
    @0
    @38
    @64
    wph
    @0
    @3
    @14
    @40
    @20
    simp1l2
    @47
    @0
    cT
    cU
    @16
    @9
    sselda
    syl2anc
    cS
    cU
    @55
    cW
    @19
    @16
    @62
    lsmcv.s
    lssvsubcl
    syl22anc
    eqeltrrd
    @41
    @43
    @44
    w3a
    #
    @1
    @17
    csn
    cN
    cfv
    cU
    @65
    cN
    cV
    cW
    cX
    @17
    @42
    lsmcv.v
    @54
    lsmcv.n
    @41
    @43
    @28
    @44
    @59
    3ad2ant1
    #
    @65
    wph
    @33
    @41
    @43
    wph
    @44
    @60
    3ad2ant1
    #
    lsmcv.x
    syl
    @38
    @39
    @15
    @20
    @43
    @44
    simp12r
    @41
    @43
    @44
    simp2
    lspsneleq
    @65
    cS
    cU
    cN
    cW
    @17
    lsmcv.s
    lsmcv.n
    @65
    @28
    @27
    @66
    @29
    syl
    @65
    wph
    @63
    @67
    lsmcv.u
    syl
    @41
    @43
    @44
    simp3
    lspsnel5a
    eqsstr3d
    mpd3an23
    3exp
    rexlimdvv
    mpd
    exlimddv
    wph
    @0
    @5
    @6
    wa
    @7
    wb
    #
    @3
    wph
    @25
    @26
    cU
    @24
    wcel
    @68
    @32
    @36
    wph
    cS
    @24
    cU
    @31
    lsmcv.u
    sseldd
    c.po
    cT
    @1
    cU
    cW
    lsmcv.p
    lsmlub
    syl3anc
    3ad2ant1
    mpbi2and
    eqssd
end
