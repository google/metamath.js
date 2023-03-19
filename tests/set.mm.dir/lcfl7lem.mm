include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wcel.mm"
include "dochsnkr2cl.mm"
include "eldifad.mm"
include "fveq2d.mm"
include "dochsnkr2.mm"
include "eqtrd.mm"
include "eqid.mm"
include "snssd.mm"
include "dochocsp.mm"
include "chlt.mm"
include "wa.mm"
include "cdih.mm"
include "crn.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "3eqtr2d.mm"
include "eleqtrd.mm"
include "clmod.mm"
include "wb.mm"
include "dvhlmod.mm"
include "lspsnel.mm"
include "mpbid.mm"
include "w3a.mm"
include "simp3.mm"
include "cur.mm"
include "cmulr.mm"
include "cinvr.mm"
include "fveq2.mm"
include "3ad2ant3.mm"
include "dochfl1.mm"
include "fveq1d.mm"
include "3eqtr4rd.mm"
include "3ad2ant1.mm"
include "dochflcl.mm"
include "simp2.mm"
include "lflmul.mm"
include "syl112anc.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "cdr.mm"
include "c0g.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "drngunz.mm"
include "eqnetrd.mm"
include "drnginvrcl.mm"
include "ringass.mm"
include "syl13anc.mm"
include "drnginvrr.mm"
include "oveq2d.mm"
include "3eqtrrd.mm"
include "ringridm.mm"
include "oveq1.mm"
include "lmodvs1.mm"
include "sylan9eqr.mm"
include "mpdan.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem lcfl7lem
  let wph: wff ph
  let vw: setvar w
  let vv: setvar v
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  assume lcfl7lem.h: |- H = ( LHyp ` K )
  assume lcfl7lem.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl7lem.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl7lem.v: |- V = ( Base ` U )
  assume lcfl7lem.a: |- .+ = ( +g ` U )
  assume lcfl7lem.t: |- .x. = ( .s ` U )
  assume lcfl7lem.s: |- S = ( Scalar ` U )
  assume lcfl7lem.r: |- R = ( Base ` S )
  assume lcfl7lem.z: |- .0. = ( 0g ` U )
  assume lcfl7lem.f: |- F = ( LFnl ` U )
  assume lcfl7lem.l: |- L = ( LKer ` U )
  assume lcfl7lem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl7lem.g: |- G = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { X } ) v = ( w .+ ( k .x. X ) ) ) )
  assume lcfl7lem.j: |- J = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { Y } ) v = ( w .+ ( k .x. Y ) ) ) )
  assume lcfl7lem.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lcfl7lem.x2: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lcfl7lem.gj: |- ( ph -> G = J )

  disjoint k v
  disjoint k w
  disjoint .+ k
  disjoint v w
  disjoint .+ v
  disjoint .+ w
  disjoint ._|_ k
  disjoint ._|_ v
  disjoint ._|_ w
  disjoint .0. w
  disjoint R k
  disjoint R v
  disjoint S k
  disjoint S w
  disjoint V v
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint k s
  disjoint s v
  disjoint R s
  disjoint s w
  disjoint S s
  disjoint U s
  disjoint V s
  disjoint .x. s
  disjoint X s
  disjoint Y s
  disjoint ph s
  assert |- ( ph -> X = Y )

  proof
    wph
    cX
    vs
    cv
    #
    cY
    c.x
    co
    #
    wceq
    #
    vs
    cR
    wrex
    #
    cX
    cY
    wceq
    #
    wph
    cX
    cY
    csn
    #
    cU
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    @3
    wph
    cX
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    @7
    wph
    cX
    @10
    c.0
    csn
    #
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcfl7lem.h
    lcfl7lem.o
    lcfl7lem.u
    lcfl7lem.v
    lcfl7lem.z
    lcfl7lem.a
    lcfl7lem.t
    lcfl7lem.l
    lcfl7lem.s
    lcfl7lem.r
    lcfl7lem.g
    lcfl7lem.k
    lcfl7lem.x
    dochsnkr2cl
    eldifad
    wph
    @10
    @5
    c.pe
    cfv
    #
    c.pe
    cfv
    @7
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @7
    wph
    @9
    @12
    c.pe
    wph
    @9
    cJ
    cL
    cfv
    @12
    wph
    cG
    cJ
    cL
    lcfl7lem.gj
    fveq2d
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    cJ
    cH
    cK
    cL
    c.pe
    cV
    cW
    cY
    c.0
    lcfl7lem.h
    lcfl7lem.o
    lcfl7lem.u
    lcfl7lem.v
    lcfl7lem.z
    lcfl7lem.a
    lcfl7lem.t
    lcfl7lem.l
    lcfl7lem.s
    lcfl7lem.r
    lcfl7lem.j
    lcfl7lem.k
    lcfl7lem.x2
    dochsnkr2
    eqtrd
    fveq2d
    wph
    @13
    @12
    c.pe
    wph
    cU
    cH
    cK
    @6
    c.pe
    cV
    cW
    @5
    lcfl7lem.h
    lcfl7lem.u
    lcfl7lem.o
    lcfl7lem.v
    @6
    eqid
    #
    lcfl7lem.k
    wph
    cY
    cV
    wph
    cY
    cV
    @11
    lcfl7lem.x2
    eldifad
    #
    snssd
    dochocsp
    fveq2d
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @7
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @14
    @7
    wceq
    lcfl7lem.k
    wph
    @17
    cY
    cV
    wcel
    #
    @19
    lcfl7lem.k
    @16
    cU
    cH
    @18
    cK
    @6
    cV
    cW
    cY
    lcfl7lem.h
    lcfl7lem.u
    lcfl7lem.v
    @15
    @18
    eqid
    #
    dihlsprn
    syl2anc
    cH
    @18
    cK
    c.pe
    cW
    @7
    lcfl7lem.h
    @21
    lcfl7lem.o
    dochoc
    syl2anc
    3eqtr2d
    eleqtrd
    wph
    cU
    clmod
    wcel
    #
    @20
    @8
    @3
    wb
    wph
    cU
    cH
    cK
    cW
    lcfl7lem.h
    lcfl7lem.u
    lcfl7lem.k
    dvhlmod
    #
    @16
    c.x
    cX
    vs
    cS
    cR
    @6
    cV
    cU
    cY
    lcfl7lem.s
    lcfl7lem.r
    lcfl7lem.v
    lcfl7lem.t
    @15
    lspsnel
    syl2anc
    mpbid
    wph
    @2
    @4
    vs
    cR
    wph
    @0
    cR
    wcel
    #
    @2
    w3a
    #
    cX
    @1
    cY
    wph
    @24
    @2
    simp3
    @25
    @0
    cS
    cur
    cfv
    #
    wceq
    #
    @1
    cY
    wceq
    @25
    @0
    @26
    cS
    cmulr
    cfv
    #
    co
    #
    cY
    cG
    cfv
    #
    @30
    cS
    cinvr
    cfv
    #
    cfv
    #
    @28
    co
    #
    @0
    @26
    @25
    @33
    @0
    @30
    @28
    co
    #
    @32
    @28
    co
    #
    @0
    @33
    @28
    co
    #
    @29
    @25
    @30
    @34
    @32
    @28
    @25
    cX
    cG
    cfv
    #
    @1
    cG
    cfv
    #
    @30
    @34
    @2
    wph
    @37
    @38
    wceq
    @24
    cX
    @1
    cG
    fveq2
    3ad2ant3
    wph
    @24
    @37
    @30
    wceq
    @2
    wph
    cY
    cJ
    cfv
    #
    @26
    @30
    @37
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    @26
    vk
    cJ
    cH
    cK
    c.pe
    cV
    cW
    cY
    c.0
    lcfl7lem.h
    lcfl7lem.o
    lcfl7lem.u
    lcfl7lem.v
    lcfl7lem.a
    lcfl7lem.t
    lcfl7lem.z
    lcfl7lem.s
    lcfl7lem.r
    @26
    eqid
    #
    lcfl7lem.k
    lcfl7lem.x2
    lcfl7lem.j
    dochfl1
    #
    wph
    cY
    cG
    cJ
    lcfl7lem.gj
    fveq1d
    #
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    @26
    vk
    cG
    cH
    cK
    c.pe
    cV
    cW
    cX
    c.0
    lcfl7lem.h
    lcfl7lem.o
    lcfl7lem.u
    lcfl7lem.v
    lcfl7lem.a
    lcfl7lem.t
    lcfl7lem.z
    lcfl7lem.s
    lcfl7lem.r
    @40
    lcfl7lem.k
    lcfl7lem.x
    lcfl7lem.g
    dochfl1
    3eqtr4rd
    3ad2ant1
    @25
    @22
    cG
    cF
    wcel
    #
    @24
    @20
    @38
    @34
    wceq
    wph
    @24
    @22
    @2
    @23
    3ad2ant1
    wph
    @24
    @43
    @2
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    cF
    cG
    cH
    cK
    c.pe
    cV
    cW
    cX
    c.0
    lcfl7lem.h
    lcfl7lem.o
    lcfl7lem.u
    lcfl7lem.v
    lcfl7lem.z
    lcfl7lem.a
    lcfl7lem.t
    lcfl7lem.f
    lcfl7lem.s
    lcfl7lem.r
    lcfl7lem.g
    lcfl7lem.k
    lcfl7lem.x
    dochflcl
    #
    3ad2ant1
    wph
    @24
    @2
    simp2
    #
    wph
    @24
    @20
    @2
    @16
    3ad2ant1
    cS
    @0
    c.x
    @28
    cF
    cG
    cR
    cV
    cU
    cY
    lcfl7lem.s
    lcfl7lem.r
    @28
    eqid
    #
    lcfl7lem.v
    lcfl7lem.t
    lcfl7lem.f
    lflmul
    syl112anc
    3eqtr3d
    oveq1d
    @25
    cS
    crg
    wcel
    #
    @24
    @30
    cR
    wcel
    #
    @32
    cR
    wcel
    #
    @35
    @36
    wceq
    wph
    @24
    @47
    @2
    wph
    @22
    @47
    @23
    cS
    cU
    lcfl7lem.s
    lmodring
    syl
    3ad2ant1
    #
    @45
    wph
    @24
    @48
    @2
    wph
    @22
    @43
    @20
    @48
    @23
    @44
    @16
    cS
    cF
    cG
    cR
    cV
    cU
    cY
    clmod
    lcfl7lem.s
    lcfl7lem.r
    lcfl7lem.v
    lcfl7lem.f
    lflcl
    syl3anc
    #
    3ad2ant1
    wph
    @24
    @49
    @2
    wph
    cS
    cdr
    wcel
    #
    @48
    @30
    cS
    c0g
    cfv
    #
    wne
    #
    @49
    wph
    cU
    clvec
    wcel
    @52
    wph
    cU
    cH
    cK
    cW
    lcfl7lem.h
    lcfl7lem.u
    lcfl7lem.k
    dvhlvec
    cS
    cU
    lcfl7lem.s
    lvecdrng
    syl
    #
    @51
    wph
    @30
    @26
    @53
    wph
    @30
    @39
    @26
    @42
    @41
    eqtrd
    wph
    @52
    @26
    @53
    wne
    @55
    cS
    @26
    @53
    @53
    eqid
    #
    @40
    drngunz
    syl
    eqnetrd
    #
    cR
    cS
    @31
    @30
    @53
    lcfl7lem.r
    @56
    @31
    eqid
    #
    drnginvrcl
    syl3anc
    3ad2ant1
    cR
    cS
    @28
    @0
    @30
    @32
    lcfl7lem.r
    @46
    ringass
    syl13anc
    @25
    @33
    @26
    @0
    @28
    wph
    @24
    @33
    @26
    wceq
    #
    @2
    wph
    @52
    @48
    @54
    @59
    @55
    @51
    @57
    cR
    cS
    @28
    @26
    @31
    @30
    @53
    lcfl7lem.r
    @56
    @46
    @40
    @58
    drnginvrr
    syl3anc
    3ad2ant1
    #
    oveq2d
    3eqtrrd
    @25
    @47
    @24
    @29
    @0
    wceq
    @50
    @45
    cR
    cS
    @28
    @26
    @0
    lcfl7lem.r
    @46
    @40
    ringridm
    syl2anc
    @60
    3eqtr3d
    @27
    @25
    @1
    @26
    cY
    c.x
    co
    #
    cY
    @0
    @26
    cY
    c.x
    oveq1
    wph
    @24
    @61
    cY
    wceq
    #
    @2
    wph
    @22
    @20
    @62
    @23
    @16
    c.x
    @26
    cS
    cV
    cU
    cY
    lcfl7lem.v
    lcfl7lem.s
    lcfl7lem.t
    @40
    lmodvs1
    syl2anc
    3ad2ant1
    sylan9eqr
    mpdan
    eqtrd
    rexlimdv3a
    mpd
end
