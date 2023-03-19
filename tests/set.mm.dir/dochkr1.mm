include "cv.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "wrex.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
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
include "drnginvrn0.mm"
include "adantr.mm"
include "lfl0.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "3impia.mm"
include "lvecvsn0.mm"
include "mpbir2and.mm"
include "sylanbrc.mm"
include "cmulr.mm"
include "lflmul.mm"
include "syl112anc.mm"
include "drnginvrl.mm"
include "eqtrd.mm"
include "rspcev.mm"
include "rexlimdv3a.mm"

theorem dochkr1
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
  assume dochkr1.h: |- H = ( LHyp ` K )
  assume dochkr1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochkr1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochkr1.v: |- V = ( Base ` U )
  assume dochkr1.r: |- R = ( Scalar ` U )
  assume dochkr1.z: |- .0. = ( 0g ` U )
  assume dochkr1.i: |- .1. = ( 1r ` R )
  assume dochkr1.f: |- F = ( LFnl ` U )
  assume dochkr1.l: |- L = ( LKer ` U )
  assume dochkr1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochkr1.g: |- ( ph -> G e. F )
  assume dochkr1.n: |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V )

  disjoint .0. x
  disjoint G x
  disjoint L x
  disjoint R x
  disjoint U x
  disjoint ._|_ x
  disjoint .1. x
  disjoint x z
  disjoint .0. z
  disjoint G z
  disjoint L z
  disjoint ph z
  disjoint U z
  disjoint ._|_ z
  disjoint .1. z
  assert |- ( ph -> E. x e. ( ( ._|_ ` ( L ` G ) ) \ { .0. } ) ( G ` x ) = .1. )

  proof
    wph
    vz
    cv
    #
    cG
    cfv
    #
    cR
    c0g
    cfv
    #
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
    @5
    c.0
    csn
    cdif
    #
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
    @5
    wrex
    @6
    wph
    vz
    cU
    clsa
    cfv
    #
    @5
    cU
    @12
    @12
    eqid
    #
    @14
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    dochkr1.h
    dochkr1.u
    dochkr1.k
    dvhlmod
    #
    wph
    @5
    c.pe
    cfv
    cV
    wne
    @5
    @14
    wcel
    dochkr1.n
    wph
    @14
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    dochkr1.h
    dochkr1.o
    dochkr1.u
    dochkr1.v
    @16
    dochkr1.f
    dochkr1.l
    dochkr1.k
    dochkr1.g
    dochkrsat2
    mpbid
    lsateln0
    wph
    @13
    @3
    vz
    @5
    wph
    @0
    @5
    wcel
    #
    wa
    #
    @13
    @3
    @19
    @13
    wa
    cR
    cU
    cF
    cG
    cH
    cK
    cL
    @2
    c.pe
    cV
    cW
    @0
    @12
    dochkr1.h
    dochkr1.o
    dochkr1.u
    dochkr1.v
    dochkr1.r
    @2
    eqid
    #
    @15
    dochkr1.f
    dochkr1.l
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @18
    @13
    dochkr1.k
    ad2antrr
    wph
    cG
    cF
    wcel
    #
    @18
    @13
    dochkr1.g
    ad2antrr
    @18
    @13
    @0
    @5
    @12
    csn
    cdif
    wcel
    #
    wph
    @23
    @18
    @13
    wa
    @0
    @5
    @12
    eldifsn
    biimpri
    adantll
    dochfln0
    ex
    reximdva
    mpd
    wph
    @3
    @11
    vz
    @5
    wph
    @18
    @3
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
    @10
    wcel
    #
    @28
    cG
    cfv
    #
    c.1
    wceq
    #
    @11
    @24
    @28
    @5
    wcel
    #
    @28
    c.0
    wne
    #
    @29
    @24
    cU
    clmod
    wcel
    #
    @5
    cU
    clss
    cfv
    #
    wcel
    #
    wa
    #
    @26
    cR
    cbs
    cfv
    #
    wcel
    #
    @18
    wa
    @32
    wph
    @18
    @37
    @3
    wph
    @34
    @36
    @17
    wph
    @21
    @4
    cV
    wss
    #
    @36
    dochkr1.k
    wph
    cF
    cG
    cL
    cV
    cU
    dochkr1.v
    dochkr1.f
    dochkr1.l
    @17
    dochkr1.g
    lkrssv
    #
    @35
    cU
    cH
    cK
    c.pe
    cV
    cW
    @4
    dochkr1.h
    dochkr1.u
    dochkr1.v
    @35
    eqid
    #
    dochkr1.o
    dochlss
    syl2anc
    jca
    3ad2ant1
    @24
    @39
    @18
    @24
    cR
    cdr
    wcel
    #
    @1
    @38
    wcel
    #
    @3
    @39
    @24
    cU
    clvec
    wcel
    #
    @43
    wph
    @18
    @45
    @3
    wph
    cU
    cH
    cK
    cW
    dochkr1.h
    dochkr1.u
    dochkr1.k
    dvhlvec
    3ad2ant1
    #
    cR
    cU
    dochkr1.r
    lvecdrng
    syl
    #
    @24
    @34
    @22
    @0
    cV
    wcel
    #
    @44
    wph
    @18
    @34
    @3
    @17
    3ad2ant1
    #
    wph
    @18
    @22
    @3
    dochkr1.g
    3ad2ant1
    #
    wph
    @18
    @48
    @3
    wph
    @5
    cV
    @0
    wph
    @21
    @40
    @5
    cV
    wss
    dochkr1.k
    @41
    cU
    cH
    cK
    c.pe
    cV
    cW
    @4
    dochkr1.h
    dochkr1.u
    dochkr1.v
    dochkr1.o
    dochssv
    syl2anc
    sselda
    3adant3
    #
    cR
    cF
    cG
    @38
    cV
    cU
    @0
    clmod
    dochkr1.r
    @38
    eqid
    #
    dochkr1.v
    dochkr1.f
    lflcl
    syl3anc
    #
    wph
    @18
    @3
    simp3
    #
    @38
    cR
    @25
    @1
    @2
    @52
    @20
    @25
    eqid
    #
    drnginvrcl
    syl3anc
    #
    wph
    @18
    @3
    simp2
    jca
    @38
    @35
    @27
    @5
    cR
    cU
    @26
    @0
    dochkr1.r
    @27
    eqid
    #
    @52
    @42
    lssvscl
    syl2anc
    @24
    @33
    @26
    @2
    wne
    #
    @0
    c.0
    wne
    #
    @24
    @43
    @44
    @3
    @58
    @47
    @53
    @54
    @38
    cR
    @25
    @1
    @2
    @52
    @20
    @55
    drnginvrn0
    syl3anc
    wph
    @18
    @3
    @59
    @19
    @0
    c.0
    @1
    @2
    @19
    @1
    @2
    wceq
    @0
    c.0
    wceq
    #
    c.0
    cG
    cfv
    #
    @2
    wceq
    #
    @19
    @34
    @22
    @62
    wph
    @34
    @18
    @17
    adantr
    wph
    @22
    @18
    dochkr1.g
    adantr
    cR
    cF
    cG
    cU
    @2
    c.0
    dochkr1.r
    @20
    dochkr1.z
    dochkr1.f
    lfl0
    syl2anc
    @60
    @1
    @61
    @2
    @0
    c.0
    cG
    fveq2
    eqeq1d
    syl5ibrcom
    necon3d
    3impia
    @24
    @26
    @27
    cR
    @38
    @2
    cV
    cU
    @0
    c.0
    dochkr1.v
    @57
    dochkr1.r
    @52
    @20
    dochkr1.z
    @46
    @56
    @51
    lvecvsn0
    mpbir2and
    @28
    @5
    c.0
    eldifsn
    sylanbrc
    @24
    @30
    @26
    @1
    cR
    cmulr
    cfv
    #
    co
    #
    c.1
    @24
    @34
    @22
    @39
    @48
    @30
    @64
    wceq
    @49
    @50
    @56
    @51
    cR
    @26
    @27
    @63
    cF
    cG
    @38
    cV
    cU
    @0
    dochkr1.r
    @52
    @63
    eqid
    #
    dochkr1.v
    @57
    dochkr1.f
    lflmul
    syl112anc
    @24
    @43
    @44
    @3
    @64
    c.1
    wceq
    @47
    @53
    @54
    @38
    cR
    @63
    c.1
    @25
    @1
    @2
    @52
    @20
    @65
    dochkr1.i
    @55
    drnginvrl
    syl3anc
    eqtrd
    @9
    @31
    vx
    @28
    @10
    @7
    @28
    wceq
    @8
    @30
    c.1
    @7
    @28
    cG
    fveq2
    eqeq1d
    rspcev
    syl2anc
    rexlimdv3a
    mpd
end
