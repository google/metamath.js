include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wrex.mm"
include "ciun.mm"
include "csn.mm"
include "eldifad.mm"
include "syl6eleq.mm"
include "eliun.mm"
include "sylib.mm"
include "w3a.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "cbs.mm"
include "lssel.mm"
include "sylan.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "ldualvbase.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "3adant3.mm"
include "cdif.mm"
include "wss.mm"
include "wral.mm"
include "chlt.mm"
include "lkrssv.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "ssdifd.mm"
include "sseldd.mm"
include "lcfrlem10.mm"
include "clsa.mm"
include "wne.mm"
include "simp3.mm"
include "eldifsni.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "dochsnkrlem2.mm"
include "lcfrlem15.mm"
include "lsat2el.mm"
include "cdih.mm"
include "crn.mm"
include "simp2.mm"
include "lcfl5.mm"
include "mpbid.mm"
include "lcfrlem13.mm"
include "doch11.mm"
include "eqlkr4.mm"
include "simpr.mm"
include "simpl2.mm"
include "ldualssvscl.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "rexlimdv3a.mm"

theorem lcfrlem16
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let cD: class D
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cE: class E
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
  let c.0: class .0.
  assume lcf1o.h: |- H = ( LHyp ` K )
  assume lcf1o.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcf1o.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcf1o.v: |- V = ( Base ` U )
  assume lcf1o.a: |- .+ = ( +g ` U )
  assume lcf1o.t: |- .x. = ( .s ` U )
  assume lcf1o.s: |- S = ( Scalar ` U )
  assume lcf1o.r: |- R = ( Base ` S )
  assume lcf1o.z: |- .0. = ( 0g ` U )
  assume lcf1o.f: |- F = ( LFnl ` U )
  assume lcf1o.l: |- L = ( LKer ` U )
  assume lcf1o.d: |- D = ( LDual ` U )
  assume lcf1o.q: |- Q = ( 0g ` D )
  assume lcf1o.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcf1o.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )
  assume lcflo.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem16.p: |- P = ( LSubSp ` D )
  assume lcfrlem16.g: |- ( ph -> G e. P )
  assume lcfrlem16.gs: |- ( ph -> G C_ C )
  assume lcfrlem16.m: |- E = U_ g e. G ( ._|_ ` ( L ` g ) )
  assume lcfrlem16.x: |- ( ph -> X e. ( E \ { .0. } ) )

  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .0. x
  disjoint v x
  disjoint V v
  disjoint V x
  disjoint .x. x
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint X k
  disjoint v w
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint .+ x
  disjoint R x
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint .+ f
  disjoint .+ k
  disjoint .+ v
  disjoint .+ w
  disjoint F f
  disjoint F k
  disjoint g k
  disjoint G g
  disjoint G k
  disjoint f g
  disjoint J f
  disjoint J g
  disjoint J k
  disjoint L f
  disjoint L k
  disjoint ._|_ f
  disjoint ._|_ k
  disjoint ._|_ v
  disjoint R f
  disjoint R k
  disjoint R v
  disjoint S k
  disjoint .x. f
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint U k
  disjoint V f
  disjoint V g
  disjoint f x
  disjoint X f
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint X g
  disjoint g ph
  disjoint k ph
  assert |- ( ph -> ( J ` X ) e. G )

  proof
    wph
    cX
    vg
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    wcel
    #
    vg
    cG
    wrex
    #
    cX
    cJ
    cfv
    #
    cG
    wcel
    #
    wph
    cX
    vg
    cG
    @2
    ciun
    #
    wcel
    @4
    wph
    cX
    cE
    @7
    wph
    cX
    cE
    c.0
    csn
    #
    lcfrlem16.x
    eldifad
    lcfrlem16.m
    syl6eleq
    vg
    cX
    cG
    @2
    eliun
    sylib
    wph
    @3
    @6
    vg
    cG
    wph
    @0
    cG
    wcel
    #
    @3
    w3a
    #
    @5
    vk
    cv
    #
    @0
    cD
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vk
    cR
    wrex
    @6
    @10
    cD
    cR
    cS
    @12
    cF
    @0
    @5
    cL
    cU
    vk
    lcf1o.s
    lcf1o.r
    lcf1o.f
    lcf1o.l
    lcf1o.d
    @12
    eqid
    #
    wph
    @9
    cU
    clvec
    wcel
    @3
    wph
    cU
    cH
    cK
    cW
    lcf1o.h
    lcf1o.u
    lcflo.k
    dvhlvec
    3ad2ant1
    #
    wph
    @9
    @0
    cF
    wcel
    @3
    wph
    @9
    wa
    #
    @0
    cD
    cbs
    cfv
    #
    cF
    wph
    cG
    cP
    wcel
    #
    @9
    @0
    @18
    wcel
    lcfrlem16.g
    cP
    cG
    @18
    cD
    @0
    @18
    eqid
    #
    lcfrlem16.p
    lssel
    sylan
    wph
    @18
    cF
    wceq
    @9
    wph
    cD
    cF
    @18
    cU
    clmod
    lcf1o.f
    lcf1o.d
    @20
    wph
    cU
    cH
    cK
    cW
    lcf1o.h
    lcf1o.u
    lcflo.k
    dvhlmod
    #
    ldualvbase
    adantr
    eleqtrd
    #
    3adant3
    #
    wph
    @9
    @5
    cF
    wcel
    @3
    wph
    vx
    vw
    vv
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    lcf1o.j
    lcflo.k
    wph
    cE
    @8
    cdif
    #
    cV
    @8
    cdif
    cX
    wph
    cE
    cV
    @8
    wph
    cE
    @7
    cV
    lcfrlem16.m
    wph
    @2
    cV
    wss
    #
    vg
    cG
    wral
    @7
    cV
    wss
    wph
    @25
    vg
    cG
    @17
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cV
    wss
    @25
    wph
    @26
    @9
    lcflo.k
    adantr
    @17
    cF
    @0
    cL
    cV
    cU
    lcf1o.v
    lcf1o.f
    lcf1o.l
    wph
    cU
    clmod
    wcel
    #
    @9
    @21
    adantr
    @22
    lkrssv
    cU
    cH
    cK
    c.pe
    cV
    cW
    @1
    lcf1o.h
    lcf1o.u
    lcf1o.v
    lcf1o.o
    dochssv
    syl2anc
    ralrimiva
    vg
    cG
    @2
    cV
    iunss
    sylibr
    syl5eqss
    ssdifd
    lcfrlem16.x
    sseldd
    #
    lcfrlem10
    #
    3ad2ant1
    @10
    @2
    @5
    cL
    cfv
    #
    c.pe
    cfv
    #
    wceq
    @1
    @30
    wceq
    @10
    cU
    clsa
    cfv
    #
    @2
    @31
    cU
    cX
    c.0
    lcf1o.z
    @32
    eqid
    #
    @16
    @10
    @32
    cU
    cF
    @0
    cH
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.z
    lcf1o.f
    lcf1o.l
    wph
    @9
    @26
    @3
    lcflo.k
    3ad2ant1
    #
    @23
    @10
    @3
    cX
    c.0
    wne
    #
    cX
    @2
    @8
    cdif
    wcel
    wph
    @9
    @3
    simp3
    #
    wph
    @9
    @35
    @3
    wph
    cX
    @24
    wcel
    @35
    lcfrlem16.x
    cX
    cE
    c.0
    eldifsni
    syl
    #
    3ad2ant1
    #
    cX
    @2
    c.0
    eldifsn
    sylanbrc
    @33
    dochsnkrlem2
    wph
    @9
    @31
    @32
    wcel
    @3
    wph
    @32
    cU
    cF
    @5
    cH
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcflo.k
    @29
    wph
    cX
    @31
    wcel
    #
    @35
    cX
    @31
    @8
    cdif
    wcel
    wph
    vx
    vw
    vv
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    lcf1o.j
    lcflo.k
    @28
    lcfrlem15
    #
    @37
    cX
    @31
    c.0
    eldifsn
    sylanbrc
    @33
    dochsnkrlem2
    3ad2ant1
    @38
    @36
    wph
    @9
    @39
    @3
    @40
    3ad2ant1
    lsat2el
    @10
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    cK
    c.pe
    cW
    @1
    @30
    lcf1o.h
    @41
    eqid
    #
    lcf1o.o
    @34
    @10
    @0
    cC
    wcel
    @1
    @41
    crn
    #
    wcel
    @10
    cG
    cC
    @0
    wph
    @9
    cG
    cC
    wss
    @3
    lcfrlem16.gs
    3ad2ant1
    wph
    @9
    @3
    simp2
    sseldd
    @10
    cC
    cU
    vf
    cF
    @0
    cH
    @41
    cK
    cL
    c.pe
    cW
    lcf1o.h
    @42
    lcf1o.o
    lcf1o.u
    lcf1o.f
    lcf1o.l
    lcf1o.c
    @34
    @23
    lcfl5
    mpbid
    wph
    @9
    @30
    @43
    wcel
    #
    @3
    wph
    @5
    cC
    wcel
    @44
    wph
    @5
    cC
    cQ
    csn
    wph
    vx
    vw
    vv
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    lcf1o.j
    lcflo.k
    @28
    lcfrlem13
    eldifad
    wph
    cC
    cU
    vf
    cF
    @5
    cH
    @41
    cK
    cL
    c.pe
    cW
    lcf1o.h
    @42
    lcf1o.o
    lcf1o.u
    lcf1o.f
    lcf1o.l
    lcf1o.c
    lcflo.k
    @29
    lcfl5
    mpbid
    3ad2ant1
    doch11
    mpbid
    eqlkr4
    @10
    @14
    @6
    vk
    cR
    @10
    @11
    cR
    wcel
    #
    wa
    #
    @6
    @14
    @13
    cG
    wcel
    @46
    cD
    cS
    cP
    @12
    cG
    cR
    cU
    @11
    @0
    lcf1o.s
    lcf1o.r
    lcf1o.d
    @15
    lcfrlem16.p
    @10
    @27
    @45
    wph
    @9
    @27
    @3
    @21
    3ad2ant1
    adantr
    @10
    @19
    @45
    wph
    @9
    @19
    @3
    lcfrlem16.g
    3ad2ant1
    adantr
    @10
    @45
    simpr
    wph
    @9
    @3
    @45
    simpl2
    ldualssvscl
    @5
    @13
    cG
    eleq1
    syl5ibrcom
    rexlimdva
    mpd
    rexlimdv3a
    mpd
end
