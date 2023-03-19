include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cmulr.mm"
include "cplusg.mm"
include "simp3l.mm"
include "oveq2d.mm"
include "simp3r.mm"
include "oveq12d.mm"
include "clmod.mm"
include "clvec.mm"
include "simpl1.mm"
include "lveclmod.mm"
include "3syl.mm"
include "simpl2.mm"
include "simpr2.mm"
include "simpl3.mm"
include "adantr.mm"
include "simpr.mm"
include "csn.mm"
include "lshpkrlem2.mm"
include "syl2anc.mm"
include "syl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "eqid.mm"
include "lmodvsass.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "lmodmcl.mm"
include "simpr3.mm"
include "simpr1.mm"
include "lmod4.mm"
include "syl122anc.mm"
include "lmodvsdir.mm"
include "eqtrd.mm"
include "3adant3.mm"

theorem lshpkrlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  let vl: setvar l
  let vb: setvar b
  let vz: setvar z
  assume lshpkrlem.v: |- V = ( Base ` W )
  assume lshpkrlem.a: |- .+ = ( +g ` W )
  assume lshpkrlem.n: |- N = ( LSpan ` W )
  assume lshpkrlem.p: |- .(+) = ( LSSum ` W )
  assume lshpkrlem.h: |- H = ( LSHyp ` W )
  assume lshpkrlem.w: |- ( ph -> W e. LVec )
  assume lshpkrlem.u: |- ( ph -> U e. H )
  assume lshpkrlem.z: |- ( ph -> Z e. V )
  assume lshpkrlem.x: |- ( ph -> X e. V )
  assume lshpkrlem.e: |- ( ph -> ( U .(+) ( N ` { Z } ) ) = V )
  assume lshpkrlem.d: |- D = ( Scalar ` W )
  assume lshpkrlem.k: |- K = ( Base ` D )
  assume lshpkrlem.t: |- .x. = ( .s ` W )
  assume lshpkrlem.o: |- .0. = ( 0g ` D )
  assume lshpkrlem.g: |- G = ( x e. V |-> ( iota_ k e. K E. y e. U x = ( y .+ ( k .x. Z ) ) ) )

  disjoint k x
  disjoint k y
  disjoint .+ k
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint K k
  disjoint K x
  disjoint .0. k
  disjoint .x. k
  disjoint .x. x
  disjoint .x. y
  disjoint U k
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint Z k
  disjoint Z x
  disjoint Z y
  disjoint .+ l
  disjoint G l
  disjoint K l
  disjoint U l
  disjoint X l
  disjoint Z l
  disjoint k l
  disjoint l x
  disjoint l y
  disjoint .x. l
  disjoint k u
  disjoint k v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint b k
  disjoint b x
  disjoint b y
  disjoint .+ b
  disjoint .0. b
  disjoint .x. b
  disjoint U b
  disjoint X b
  disjoint Z b
  disjoint b ph
  disjoint l z
  disjoint .+ z
  disjoint G z
  disjoint U z
  disjoint X z
  disjoint Z z
  disjoint k z
  disjoint x z
  disjoint y z
  disjoint .x. z
  assert |- ( ( ( ph /\ l e. K /\ u e. V ) /\ ( v e. V /\ r e. V /\ s e. V ) /\ ( u = ( r .+ ( ( G ` u ) .x. Z ) ) /\ v = ( s .+ ( ( G ` v ) .x. Z ) ) ) ) -> ( ( l .x. u ) .+ v ) = ( ( ( l .x. r ) .+ s ) .+ ( ( ( l ( .r ` D ) ( G ` u ) ) ( +g ` D ) ( G ` v ) ) .x. Z ) ) )

  proof
    wph
    vl
    cv
    #
    cK
    wcel
    #
    vu
    cv
    #
    cV
    wcel
    #
    w3a
    #
    vv
    cv
    #
    cV
    wcel
    #
    vr
    cv
    #
    cV
    wcel
    #
    vs
    cv
    #
    cV
    wcel
    #
    w3a
    #
    @2
    @7
    @2
    cG
    cfv
    #
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @5
    @9
    @5
    cG
    cfv
    #
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    wa
    #
    w3a
    #
    @0
    @2
    c.x
    co
    #
    @5
    c.pl
    co
    @0
    @14
    c.x
    co
    #
    @18
    c.pl
    co
    #
    @0
    @7
    c.x
    co
    #
    @9
    c.pl
    co
    #
    @0
    @12
    cD
    cmulr
    cfv
    #
    co
    #
    @16
    cD
    cplusg
    cfv
    #
    co
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    @21
    @22
    @23
    @5
    @18
    c.pl
    @21
    @2
    @14
    @0
    c.x
    @4
    @11
    @15
    @19
    simp3l
    oveq2d
    @4
    @11
    @15
    @19
    simp3r
    oveq12d
    @4
    @11
    @24
    @31
    wceq
    @20
    @4
    @11
    wa
    #
    @24
    @25
    @28
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    @18
    c.pl
    co
    #
    @31
    @32
    @23
    @34
    @18
    c.pl
    @32
    @23
    @25
    @0
    @13
    c.x
    co
    #
    c.pl
    co
    #
    @34
    @32
    cW
    clmod
    wcel
    #
    @1
    @8
    @13
    cV
    wcel
    #
    @23
    @37
    wceq
    @32
    wph
    cW
    clvec
    wcel
    #
    @38
    wph
    @1
    @3
    @11
    simpl1
    #
    lshpkrlem.w
    cW
    lveclmod
    3syl
    #
    wph
    @1
    @3
    @11
    simpl2
    #
    @4
    @6
    @8
    @10
    simpr2
    #
    @32
    @38
    @12
    cK
    wcel
    #
    cZ
    cV
    wcel
    #
    @39
    @42
    @32
    wph
    @3
    @45
    @41
    wph
    @1
    @3
    @11
    simpl3
    wph
    @3
    wa
    vx
    vy
    cD
    c.pl
    c.po
    c.x
    cU
    vk
    cG
    cH
    cK
    cN
    cV
    cW
    @2
    c.0
    cZ
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    wph
    @40
    @3
    lshpkrlem.w
    adantr
    wph
    cU
    cH
    wcel
    #
    @3
    lshpkrlem.u
    adantr
    wph
    @46
    @3
    lshpkrlem.z
    adantr
    wph
    @3
    simpr
    wph
    cU
    cZ
    csn
    cN
    cfv
    c.po
    co
    cV
    wceq
    #
    @3
    lshpkrlem.e
    adantr
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpkrlem.o
    lshpkrlem.g
    lshpkrlem2
    syl2anc
    #
    @32
    wph
    @46
    @41
    lshpkrlem.z
    syl
    #
    @12
    c.x
    cD
    cK
    cV
    cW
    cZ
    lshpkrlem.v
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    lmodvscl
    syl3anc
    c.pl
    @0
    c.x
    cD
    cK
    cV
    cW
    @7
    @13
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    lmodvsdi
    syl13anc
    @32
    @33
    @36
    @25
    c.pl
    @32
    @38
    @1
    @45
    @46
    @33
    @36
    wceq
    @42
    @43
    @49
    @50
    @0
    @12
    c.x
    @27
    cD
    cK
    cV
    cW
    cZ
    lshpkrlem.v
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    @27
    eqid
    #
    lmodvsass
    syl13anc
    oveq2d
    eqtr4d
    oveq1d
    @32
    @35
    @26
    @33
    @17
    c.pl
    co
    #
    c.pl
    co
    #
    @31
    @32
    @38
    @25
    cV
    wcel
    #
    @33
    cV
    wcel
    #
    @10
    @17
    cV
    wcel
    #
    @35
    @53
    wceq
    @42
    @32
    @38
    @1
    @8
    @54
    @42
    @43
    @44
    @0
    c.x
    cD
    cK
    cV
    cW
    @7
    lshpkrlem.v
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    lmodvscl
    syl3anc
    @32
    @38
    @28
    cK
    wcel
    #
    @46
    @55
    @42
    @32
    @38
    @1
    @45
    @57
    @42
    @43
    @49
    @27
    cD
    cK
    cW
    @0
    @12
    lshpkrlem.d
    lshpkrlem.k
    @51
    lmodmcl
    syl3anc
    #
    @50
    @28
    c.x
    cD
    cK
    cV
    cW
    cZ
    lshpkrlem.v
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    lmodvscl
    syl3anc
    @4
    @6
    @8
    @10
    simpr3
    @32
    @38
    @16
    cK
    wcel
    #
    @46
    @56
    @42
    @32
    wph
    @6
    @59
    @41
    @4
    @6
    @8
    @10
    simpr1
    wph
    @6
    wa
    vx
    vy
    cD
    c.pl
    c.po
    c.x
    cU
    vk
    cG
    cH
    cK
    cN
    cV
    cW
    @5
    c.0
    cZ
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    wph
    @40
    @6
    lshpkrlem.w
    adantr
    wph
    @47
    @6
    lshpkrlem.u
    adantr
    wph
    @46
    @6
    lshpkrlem.z
    adantr
    wph
    @6
    simpr
    wph
    @48
    @6
    lshpkrlem.e
    adantr
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpkrlem.o
    lshpkrlem.g
    lshpkrlem2
    syl2anc
    #
    @50
    @16
    c.x
    cD
    cK
    cV
    cW
    cZ
    lshpkrlem.v
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    lmodvscl
    syl3anc
    c.pl
    @17
    cV
    cW
    @25
    @33
    @9
    lshpkrlem.v
    lshpkrlem.a
    lmod4
    syl122anc
    @32
    @30
    @52
    @26
    c.pl
    @32
    @38
    @57
    @59
    @46
    @30
    @52
    wceq
    @42
    @58
    @60
    @50
    c.pl
    @29
    @28
    @16
    c.x
    cD
    cK
    cV
    cW
    cZ
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    @29
    eqid
    lmodvsdir
    syl13anc
    oveq2d
    eqtr4d
    eqtrd
    3adant3
    eqtrd
end
