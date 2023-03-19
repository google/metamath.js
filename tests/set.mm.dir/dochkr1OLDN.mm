include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "wrex.mm"
include "wceq.mm"
include "c0g.mm"
include "clsa.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "wcel.mm"
include "dochkrsat2.mm"
include "mpbid.mm"
include "lsateln0.mm"
include "wa.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "adantll.mm"
include "dochfln0.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "w3a.mm"
include "cinvr.mm"
include "cvsca.mm"
include "co.mm"
include "clmod.mm"
include "clss.mm"
include "cbs.mm"
include "wss.mm"
include "lkrssv.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "cdr.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "dochssv.mm"
include "sselda.mm"
include "3adant3.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "simp3.mm"
include "drnginvrcl.mm"
include "simp2.mm"
include "lssvscl.mm"
include "syl12anc.mm"
include "cmulr.mm"
include "lflmul.mm"
include "syl112anc.mm"
include "drnginvrl.mm"
include "eqtrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "rexlimdv3a.mm"

theorem dochkr1OLDN
  let wph: wff ph
  let vx: setvar x
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vz: setvar z
  assume dochkr1OLD.h: |- H = ( LHyp ` K )
  assume dochkr1OLD.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochkr1OLD.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochkr1OLD.v: |- V = ( Base ` U )
  assume dochkr1OLD.r: |- R = ( Scalar ` U )
  assume dochkr1OLD.z: |- .0. = ( 0g ` R )
  assume dochkr1OLD.i: |- .1. = ( 1r ` R )
  assume dochkr1OLD.f: |- F = ( LFnl ` U )
  assume dochkr1OLD.l: |- L = ( LKer ` U )
  assume dochkr1OLD.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochkr1OLD.g: |- ( ph -> G e. F )
  assume dochkr1OLD.n: |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V )

  disjoint .1. x
  disjoint G x
  disjoint L x
  disjoint R x
  disjoint U x
  disjoint ._|_ x
  disjoint x z
  disjoint .1. z
  disjoint G z
  disjoint L z
  disjoint ph z
  disjoint U z
  disjoint ._|_ z
  assert |- ( ph -> E. x e. ( ._|_ ` ( L ` G ) ) ( G ` x ) = .1. )

  proof
    wph
    vz
    cv
    #
    cG
    cfv
    #
    c.0
    wne
    #
    vz
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    wrex
    #
    vx
    cv
    #
    cG
    cfv
    #
    c.1
    wceq
    #
    vx
    @4
    wrex
    #
    wph
    @0
    cU
    c0g
    cfv
    #
    wne
    #
    vz
    @4
    wrex
    @5
    wph
    vz
    cU
    clsa
    cfv
    #
    @4
    cU
    @10
    @10
    eqid
    #
    @12
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    dochkr1OLD.h
    dochkr1OLD.u
    dochkr1OLD.k
    dvhlmod
    #
    wph
    @4
    c.pe
    cfv
    cV
    wne
    @4
    @12
    wcel
    dochkr1OLD.n
    wph
    @12
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    dochkr1OLD.h
    dochkr1OLD.o
    dochkr1OLD.u
    dochkr1OLD.v
    @14
    dochkr1OLD.f
    dochkr1OLD.l
    dochkr1OLD.k
    dochkr1OLD.g
    dochkrsat2
    mpbid
    lsateln0
    wph
    @11
    @2
    vz
    @4
    wph
    @0
    @4
    wcel
    #
    wa
    #
    @11
    @2
    @17
    @11
    wa
    cR
    cU
    cF
    cG
    cH
    cK
    cL
    c.0
    c.pe
    cV
    cW
    @0
    @10
    dochkr1OLD.h
    dochkr1OLD.o
    dochkr1OLD.u
    dochkr1OLD.v
    dochkr1OLD.r
    dochkr1OLD.z
    @13
    dochkr1OLD.f
    dochkr1OLD.l
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @16
    @11
    dochkr1OLD.k
    ad2antrr
    wph
    cG
    cF
    wcel
    #
    @16
    @11
    dochkr1OLD.g
    ad2antrr
    @16
    @11
    @0
    @4
    @10
    csn
    cdif
    wcel
    #
    wph
    @20
    @16
    @11
    wa
    @0
    @4
    @10
    eldifsn
    biimpri
    adantll
    dochfln0
    ex
    reximdva
    mpd
    wph
    @2
    @9
    vz
    @4
    wph
    @16
    @2
    w3a
    #
    @1
    cR
    cinvr
    cfv
    #
    cfv
    #
    @0
    cU
    cvsca
    cfv
    #
    co
    #
    @4
    wcel
    #
    @25
    cG
    cfv
    #
    c.1
    wceq
    #
    @9
    @21
    cU
    clmod
    wcel
    #
    @4
    cU
    clss
    cfv
    #
    wcel
    #
    wa
    #
    @23
    cR
    cbs
    cfv
    #
    wcel
    #
    @16
    @26
    wph
    @16
    @32
    @2
    wph
    @29
    @31
    @15
    wph
    @18
    @3
    cV
    wss
    #
    @31
    dochkr1OLD.k
    wph
    cF
    cG
    cL
    cV
    cU
    dochkr1OLD.v
    dochkr1OLD.f
    dochkr1OLD.l
    @15
    dochkr1OLD.g
    lkrssv
    #
    @30
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    dochkr1OLD.h
    dochkr1OLD.u
    dochkr1OLD.v
    @30
    eqid
    #
    dochkr1OLD.o
    dochlss
    syl2anc
    jca
    3ad2ant1
    @21
    cR
    cdr
    wcel
    #
    @1
    @33
    wcel
    #
    @2
    @34
    @21
    cU
    clvec
    wcel
    #
    @38
    wph
    @16
    @40
    @2
    wph
    cU
    cH
    cK
    cW
    dochkr1OLD.h
    dochkr1OLD.u
    dochkr1OLD.k
    dvhlvec
    3ad2ant1
    cR
    cU
    dochkr1OLD.r
    lvecdrng
    syl
    #
    @21
    @29
    @19
    @0
    cV
    wcel
    #
    @39
    wph
    @16
    @29
    @2
    @15
    3ad2ant1
    #
    wph
    @16
    @19
    @2
    dochkr1OLD.g
    3ad2ant1
    #
    wph
    @16
    @42
    @2
    wph
    @4
    cV
    @0
    wph
    @18
    @35
    @4
    cV
    wss
    dochkr1OLD.k
    @36
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    dochkr1OLD.h
    dochkr1OLD.u
    dochkr1OLD.v
    dochkr1OLD.o
    dochssv
    syl2anc
    sselda
    3adant3
    #
    cR
    cF
    cG
    @33
    cV
    cU
    @0
    clmod
    dochkr1OLD.r
    @33
    eqid
    #
    dochkr1OLD.v
    dochkr1OLD.f
    lflcl
    syl3anc
    #
    wph
    @16
    @2
    simp3
    #
    @33
    cR
    @22
    @1
    c.0
    @46
    dochkr1OLD.z
    @22
    eqid
    #
    drnginvrcl
    syl3anc
    #
    wph
    @16
    @2
    simp2
    @33
    @30
    @24
    @4
    cR
    cU
    @23
    @0
    dochkr1OLD.r
    @24
    eqid
    #
    @46
    @37
    lssvscl
    syl12anc
    @21
    @27
    @23
    @1
    cR
    cmulr
    cfv
    #
    co
    #
    c.1
    @21
    @29
    @19
    @34
    @42
    @27
    @53
    wceq
    @43
    @44
    @50
    @45
    cR
    @23
    @24
    @52
    cF
    cG
    @33
    cV
    cU
    @0
    dochkr1OLD.r
    @46
    @52
    eqid
    #
    dochkr1OLD.v
    @51
    dochkr1OLD.f
    lflmul
    syl112anc
    @21
    @38
    @39
    @2
    @53
    c.1
    wceq
    @41
    @47
    @48
    @33
    cR
    @52
    c.1
    @22
    @1
    c.0
    @46
    dochkr1OLD.z
    @54
    dochkr1OLD.i
    @49
    drnginvrl
    syl3anc
    eqtrd
    @8
    @28
    vx
    @25
    @4
    @6
    @25
    wceq
    @7
    @27
    c.1
    @6
    @25
    cG
    fveq2
    eqeq1d
    rspcev
    syl2anc
    rexlimdv3a
    mpd
end
