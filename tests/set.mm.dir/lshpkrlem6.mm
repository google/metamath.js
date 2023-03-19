include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cmulr.mm"
include "cplusg.mm"
include "clvec.mm"
include "adantr.mm"
include "simpr2.mm"
include "csn.mm"
include "lshpkrlem3.mm"
include "simpr3.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "simpr1.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmodvacl.mm"
include "3reeanv.mm"
include "wi.mm"
include "simp1l.mm"
include "simp1r1.mm"
include "simp1r2.mm"
include "simp1r3.mm"
include "simp2ll.mm"
include "simp2lr.mm"
include "simp2r.mm"
include "jca.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "lshpkrlem5.mm"
include "syl333anc.mm"
include "3exp.mm"
include "expdimp.mm"
include "rexlimdv.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp3and.mm"

theorem lshpkrlem6
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
  let vl: setvar l
  let vb: setvar b
  let vz: setvar z
  let vr: setvar r
  let vs: setvar s
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
  disjoint l u
  disjoint l v
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
  disjoint r s
  disjoint .+ r
  disjoint .+ s
  disjoint r z
  disjoint D r
  disjoint s z
  disjoint D s
  disjoint D z
  disjoint G r
  disjoint G s
  disjoint K r
  disjoint K s
  disjoint K z
  disjoint .x. r
  disjoint .x. s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint V z
  disjoint Z r
  disjoint Z s
  disjoint ph r
  disjoint ph s
  disjoint ph z
  disjoint k r
  disjoint k s
  disjoint l r
  disjoint l s
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint u z
  disjoint v z
  assert |- ( ( ph /\ ( l e. K /\ u e. V /\ v e. V ) ) -> ( G ` ( ( l .x. u ) .+ v ) ) = ( ( l ( .r ` D ) ( G ` u ) ) ( +g ` D ) ( G ` v ) ) )

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
    vv
    cv
    #
    cV
    wcel
    #
    w3a
    #
    wa
    #
    @2
    vr
    cv
    #
    @2
    cG
    cfv
    #
    cZ
    c.x
    co
    c.pl
    co
    wceq
    #
    vr
    cU
    wrex
    #
    @4
    vs
    cv
    #
    @4
    cG
    cfv
    #
    cZ
    c.x
    co
    c.pl
    co
    wceq
    #
    vs
    cU
    wrex
    #
    @0
    @2
    c.x
    co
    #
    @4
    c.pl
    co
    #
    vz
    cv
    #
    @17
    cG
    cfv
    #
    cZ
    c.x
    co
    c.pl
    co
    wceq
    #
    vz
    cU
    wrex
    #
    @19
    @0
    @9
    cD
    cmulr
    cfv
    co
    @13
    cD
    cplusg
    cfv
    co
    wceq
    #
    @7
    vx
    vy
    vr
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
    cW
    clvec
    wcel
    #
    @6
    lshpkrlem.w
    adantr
    #
    wph
    cU
    cH
    wcel
    @6
    lshpkrlem.u
    adantr
    #
    wph
    cZ
    cV
    wcel
    @6
    lshpkrlem.z
    adantr
    #
    wph
    @1
    @3
    @5
    simpr2
    #
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
    @6
    lshpkrlem.e
    adantr
    #
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpkrlem.o
    lshpkrlem.g
    lshpkrlem3
    @7
    vx
    vy
    vs
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
    @4
    c.0
    cZ
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    @24
    @25
    @26
    wph
    @1
    @3
    @5
    simpr3
    #
    @28
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpkrlem.o
    lshpkrlem.g
    lshpkrlem3
    @7
    vx
    vy
    vz
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
    @17
    c.0
    cZ
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    @24
    @25
    @26
    @7
    cW
    clmod
    wcel
    #
    @16
    cV
    wcel
    #
    @5
    @17
    cV
    wcel
    @7
    @23
    @30
    @24
    cW
    lveclmod
    syl
    #
    @7
    @30
    @1
    @3
    @31
    @32
    wph
    @1
    @3
    @5
    simpr1
    @27
    @0
    c.x
    cD
    cK
    cV
    cW
    @2
    lshpkrlem.v
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    lmodvscl
    syl3anc
    @29
    c.pl
    cV
    cW
    @16
    @4
    lshpkrlem.v
    lshpkrlem.a
    lmodvacl
    syl3anc
    @28
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpkrlem.o
    lshpkrlem.g
    lshpkrlem3
    @11
    @15
    @21
    w3a
    @10
    @14
    @20
    w3a
    #
    vz
    cU
    wrex
    #
    vs
    cU
    wrex
    vr
    cU
    wrex
    @7
    @22
    @10
    @14
    @20
    vr
    vs
    vz
    cU
    cU
    cU
    3reeanv
    @7
    @34
    @22
    vr
    vs
    cU
    cU
    @7
    @8
    cU
    wcel
    #
    @12
    cU
    wcel
    #
    wa
    #
    wa
    @33
    @22
    vz
    cU
    @7
    @37
    @18
    cU
    wcel
    #
    @33
    @22
    wi
    @7
    @37
    @38
    wa
    #
    @33
    @22
    @7
    @39
    @33
    w3a
    #
    wph
    @1
    @3
    @5
    @35
    @36
    @38
    wa
    @10
    @14
    @20
    @22
    wph
    @6
    @39
    @33
    simp1l
    @1
    @3
    @5
    wph
    @39
    @33
    simp1r1
    @1
    @3
    @5
    wph
    @39
    @33
    simp1r2
    @1
    @3
    @5
    wph
    @39
    @33
    simp1r3
    @35
    @36
    @38
    @7
    @33
    simp2ll
    @40
    @36
    @38
    @35
    @36
    @38
    @7
    @33
    simp2lr
    @7
    @37
    @38
    @33
    simp2r
    jca
    @7
    @39
    @10
    @14
    @20
    simp31
    @7
    @39
    @10
    @14
    @20
    simp32
    @7
    @39
    @10
    @14
    @20
    simp33
    wph
    vx
    vy
    vz
    vv
    vu
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
    cZ
    c.0
    cZ
    vs
    vr
    vl
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    lshpkrlem.w
    lshpkrlem.u
    lshpkrlem.z
    lshpkrlem.z
    lshpkrlem.e
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpkrlem.o
    lshpkrlem.g
    lshpkrlem5
    syl333anc
    3exp
    expdimp
    rexlimdv
    rexlimdvva
    syl5bir
    mp3and
end
