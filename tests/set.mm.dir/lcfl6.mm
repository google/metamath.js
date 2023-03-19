include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "csn.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "cdif.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "cur.mm"
include "eqid.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "lcfl2.mm"
include "biimpa.mm"
include "orcomd.mm"
include "ord.mm"
include "syl5bi.mm"
include "imp.mm"
include "dochkr1.mm"
include "wss.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "ssdifd.mm"
include "ad3antrrr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "lcfl6lem.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "syl5bir.mm"
include "orrd.mm"
include "olc.mm"
include "syl5ibr.mm"
include "w3a.mm"
include "cdih.mm"
include "crn.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "snssd.mm"
include "dochcl.mm"
include "dochoc.mm"
include "3adant3.mm"
include "simp3.mm"
include "fveq2d.mm"
include "simpr.mm"
include "dochsnkr2.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "3ad2ant1.mm"
include "lcfl1.mm"
include "mpbird.mm"
include "rexlimdv3a.mm"
include "jaod.mm"
include "impbid.mm"

theorem lcfl6
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lcfl6.h: |- H = ( LHyp ` K )
  assume lcfl6.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl6.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl6.v: |- V = ( Base ` U )
  assume lcfl6.a: |- .+ = ( +g ` U )
  assume lcfl6.t: |- .x. = ( .s ` U )
  assume lcfl6.s: |- S = ( Scalar ` U )
  assume lcfl6.r: |- R = ( Base ` S )
  assume lcfl6.z: |- .0. = ( 0g ` U )
  assume lcfl6.f: |- F = ( LFnl ` U )
  assume lcfl6.l: |- L = ( LKer ` U )
  assume lcfl6.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl6.g: |- ( ph -> G e. F )

  disjoint k v
  disjoint k w
  disjoint .+ k
  disjoint v w
  disjoint .+ v
  disjoint .+ w
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint ._|_ f
  disjoint k x
  disjoint ._|_ k
  disjoint v x
  disjoint ._|_ v
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .0. w
  disjoint .0. x
  disjoint C x
  disjoint G f
  disjoint G x
  disjoint F f
  disjoint L f
  disjoint L x
  disjoint ph x
  disjoint R k
  disjoint R v
  disjoint S k
  disjoint S w
  disjoint S x
  disjoint V v
  disjoint V x
  disjoint U x
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  assert |- ( ph -> ( G e. C <-> ( ( L ` G ) = V \/ E. x e. ( V \ { .0. } ) G = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) ) ) )

  proof
    wph
    cG
    cC
    wcel
    #
    cG
    cL
    cfv
    #
    cV
    wceq
    #
    cG
    vv
    cV
    vv
    cv
    vw
    cv
    vk
    cv
    vx
    cv
    #
    c.x
    co
    c.pl
    co
    wceq
    vw
    @3
    csn
    #
    c.pe
    cfv
    #
    wrex
    vk
    cR
    crio
    cmpt
    #
    wceq
    #
    vx
    cV
    c.0
    csn
    #
    cdif
    #
    wrex
    #
    wo
    #
    wph
    @0
    @11
    wph
    @0
    wa
    #
    @2
    @10
    @2
    wn
    #
    @1
    cV
    wne
    #
    @12
    @10
    @1
    cV
    df-ne
    #
    @12
    @14
    @10
    @12
    @14
    wa
    #
    @3
    cG
    cfv
    cS
    cur
    cfv
    #
    wceq
    #
    vx
    @1
    c.pe
    cfv
    #
    @8
    cdif
    #
    wrex
    @10
    @16
    vx
    cS
    cU
    @17
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    c.0
    lcfl6.h
    lcfl6.o
    lcfl6.u
    lcfl6.v
    lcfl6.s
    lcfl6.z
    @17
    eqid
    #
    lcfl6.f
    lcfl6.l
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @0
    @14
    lcfl6.k
    ad2antrr
    wph
    cG
    cF
    wcel
    #
    @0
    @14
    lcfl6.g
    ad2antrr
    @12
    @14
    @19
    c.pe
    cfv
    #
    cV
    wne
    #
    @14
    @13
    @12
    @25
    @15
    @12
    @2
    @25
    @12
    @25
    @2
    wph
    @0
    @25
    @2
    wo
    #
    wph
    cC
    cU
    vf
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    lcfl6.h
    lcfl6.o
    lcfl6.u
    lcfl6.v
    lcfl6.f
    lcfl6.l
    lcfl6.c
    lcfl6.k
    lcfl6.g
    lcfl2
    #
    biimpa
    orcomd
    ord
    syl5bi
    imp
    dochkr1
    @16
    @18
    @7
    vx
    @20
    @9
    @16
    @3
    @20
    wcel
    #
    @18
    wa
    #
    @3
    @9
    wcel
    #
    @7
    wa
    @16
    @29
    wa
    #
    @30
    @7
    @31
    @20
    @9
    @3
    wph
    @20
    @9
    wss
    @0
    @14
    @29
    wph
    @19
    cV
    @8
    wph
    @22
    @1
    cV
    wss
    @19
    cV
    wss
    lcfl6.k
    wph
    cF
    cG
    cL
    cV
    cU
    lcfl6.v
    lcfl6.f
    lcfl6.l
    wph
    cU
    cH
    cK
    cW
    lcfl6.h
    lcfl6.u
    lcfl6.k
    dvhlmod
    lcfl6.g
    lkrssv
    cU
    cH
    cK
    c.pe
    cV
    cW
    @1
    lcfl6.h
    lcfl6.u
    lcfl6.v
    lcfl6.o
    dochssv
    syl2anc
    ssdifd
    ad3antrrr
    @16
    @28
    @18
    simprl
    #
    sseldd
    @31
    vw
    vv
    c.pl
    cR
    cS
    c.x
    cU
    @17
    vk
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    @3
    c.0
    lcfl6.h
    lcfl6.o
    lcfl6.u
    lcfl6.v
    lcfl6.a
    lcfl6.t
    lcfl6.s
    @21
    lcfl6.r
    lcfl6.z
    lcfl6.f
    lcfl6.l
    wph
    @22
    @0
    @14
    @29
    lcfl6.k
    ad3antrrr
    wph
    @23
    @0
    @14
    @29
    lcfl6.g
    ad3antrrr
    @32
    @16
    @28
    @18
    simprr
    lcfl6lem
    jca
    ex
    reximdv2
    mpd
    ex
    syl5bir
    orrd
    ex
    wph
    @2
    @0
    @10
    @2
    @0
    wph
    @26
    @2
    @25
    olc
    @27
    syl5ibr
    wph
    @7
    @0
    vx
    @9
    wph
    @30
    @7
    w3a
    #
    @0
    @24
    @1
    wceq
    @33
    @5
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @5
    @24
    @1
    wph
    @30
    @35
    @5
    wceq
    #
    @7
    wph
    @30
    wa
    #
    @22
    @5
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @36
    wph
    @22
    @30
    lcfl6.k
    adantr
    #
    @37
    @22
    @4
    cV
    wss
    @39
    @40
    @37
    @3
    cV
    @30
    @3
    cV
    wcel
    wph
    @3
    cV
    @8
    eldifi
    adantl
    snssd
    cU
    cH
    @38
    cK
    c.pe
    cV
    cW
    @4
    lcfl6.h
    @38
    eqid
    #
    lcfl6.u
    lcfl6.v
    lcfl6.o
    dochcl
    syl2anc
    cH
    @38
    cK
    c.pe
    cW
    @5
    lcfl6.h
    @41
    lcfl6.o
    dochoc
    syl2anc
    3adant3
    @33
    @19
    @34
    c.pe
    @33
    @1
    @5
    c.pe
    @33
    @1
    @6
    cL
    cfv
    #
    @5
    @33
    cG
    @6
    cL
    wph
    @30
    @7
    simp3
    fveq2d
    wph
    @30
    @42
    @5
    wceq
    @7
    @37
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    @6
    cH
    cK
    cL
    c.pe
    cV
    cW
    @3
    c.0
    lcfl6.h
    lcfl6.o
    lcfl6.u
    lcfl6.v
    lcfl6.z
    lcfl6.a
    lcfl6.t
    lcfl6.l
    lcfl6.s
    lcfl6.r
    @6
    eqid
    @40
    wph
    @30
    simpr
    dochsnkr2
    3adant3
    eqtrd
    #
    fveq2d
    fveq2d
    @43
    3eqtr4d
    @33
    cC
    vf
    cF
    cG
    cL
    c.pe
    lcfl6.c
    wph
    @30
    @23
    @7
    lcfl6.g
    3ad2ant1
    lcfl1
    mpbird
    rexlimdv3a
    jaod
    impbid
end
