include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cmulr.mm"
include "cplusg.mm"
include "csn.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "clss.mm"
include "csubg.mm"
include "clmod.mm"
include "wss.mm"
include "clvec.mm"
include "simp11.mm"
include "syl.mm"
include "lveclmod.mm"
include "lsssssubg.mm"
include "lshplss.mm"
include "sseldd.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "cin.mm"
include "lshpdisj.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "simp23r.mm"
include "simp12.mm"
include "simp22.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "simp23l.mm"
include "lssvacl.mm"
include "simp13.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "simp21.mm"
include "lmodvacl.mm"
include "adantr.mm"
include "simpr.mm"
include "lshpkrlem2.mm"
include "lspsneli.mm"
include "lmodmcl.mm"
include "lmodacl.mm"
include "simp33.mm"
include "simp1.mm"
include "lssel.mm"
include "simp31.mm"
include "simp32.mm"
include "lshpkrlem4.mm"
include "syl132anc.mm"
include "eqtr3d.mm"
include "subgdisj2.mm"
include "wne.mm"
include "lshpne0.mm"
include "lvecvscan2.mm"
include "mpbid.mm"

theorem lshpkrlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  disjoint l z
  disjoint .+ l
  disjoint .+ z
  disjoint G l
  disjoint G z
  disjoint K l
  disjoint U l
  disjoint U z
  disjoint X l
  disjoint X z
  disjoint Z l
  disjoint Z z
  disjoint k l
  disjoint k z
  disjoint l x
  disjoint l y
  disjoint x z
  disjoint y z
  disjoint .x. l
  disjoint .x. z
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
  assert |- ( ( ( ph /\ l e. K /\ u e. V ) /\ ( v e. V /\ r e. U /\ ( s e. U /\ z e. U ) ) /\ ( u = ( r .+ ( ( G ` u ) .x. Z ) ) /\ v = ( s .+ ( ( G ` v ) .x. Z ) ) /\ ( ( l .x. u ) .+ v ) = ( z .+ ( ( G ` ( ( l .x. u ) .+ v ) ) .x. Z ) ) ) ) -> ( G ` ( ( l .x. u ) .+ v ) ) = ( ( l ( .r ` D ) ( G ` u ) ) ( +g ` D ) ( G ` v ) ) )

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
    cU
    wcel
    #
    vs
    cv
    #
    cU
    wcel
    #
    vz
    cv
    #
    cU
    wcel
    #
    wa
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
    c.pl
    co
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
    c.pl
    co
    wceq
    #
    @0
    @2
    c.x
    co
    #
    @5
    c.pl
    co
    #
    @11
    @20
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
    w3a
    #
    w3a
    #
    @22
    @0
    @15
    cD
    cmulr
    cfv
    #
    co
    #
    @17
    cD
    cplusg
    cfv
    #
    co
    #
    cZ
    c.x
    co
    #
    wceq
    @21
    @30
    wceq
    @26
    @11
    @22
    @0
    @7
    c.x
    co
    #
    @9
    c.pl
    co
    #
    @31
    c.pl
    cU
    cZ
    csn
    cN
    cfv
    #
    cW
    cW
    c0g
    cfv
    #
    cW
    ccntz
    cfv
    #
    lshpkrlem.a
    @35
    eqid
    #
    @36
    eqid
    #
    @26
    cW
    clss
    cfv
    #
    cW
    csubg
    cfv
    #
    cU
    @26
    cW
    clmod
    wcel
    #
    @39
    @40
    wss
    @26
    cW
    clvec
    wcel
    #
    @41
    @26
    wph
    @42
    wph
    @1
    @3
    @14
    @25
    simp11
    #
    lshpkrlem.w
    syl
    #
    cW
    lveclmod
    #
    syl
    #
    @39
    cW
    @39
    eqid
    #
    lsssssubg
    syl
    #
    @26
    wph
    cU
    @39
    wcel
    #
    @43
    wph
    @39
    cU
    cH
    cW
    @47
    lshpkrlem.h
    wph
    @42
    @41
    lshpkrlem.w
    @45
    syl
    #
    lshpkrlem.u
    lshplss
    syl
    #
    sseldd
    #
    @26
    @39
    @40
    @34
    @48
    @26
    @41
    cZ
    cV
    wcel
    #
    @34
    @39
    wcel
    @46
    @26
    wph
    @53
    @43
    lshpkrlem.z
    syl
    #
    @39
    cN
    cV
    cW
    cZ
    lshpkrlem.v
    @47
    lshpkrlem.n
    lspsncl
    syl2anc
    sseldd
    #
    @26
    wph
    cU
    @34
    cin
    @35
    csn
    wceq
    @43
    wph
    c.po
    cU
    cH
    cN
    cV
    cW
    cZ
    @35
    lshpkrlem.v
    @37
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    lshpkrlem.w
    lshpkrlem.u
    lshpkrlem.z
    lshpkrlem.e
    lshpdisj
    syl
    @26
    cU
    @34
    cW
    @36
    @38
    @26
    @41
    cW
    cabl
    wcel
    @46
    cW
    lmodabl
    syl
    @52
    @55
    ablcntzd
    @10
    @12
    @6
    @8
    @4
    @25
    simp23r
    @26
    @41
    @49
    @32
    cU
    wcel
    #
    @10
    @33
    cU
    wcel
    @46
    @51
    @26
    @41
    @49
    @1
    @8
    @56
    @46
    @51
    wph
    @1
    @3
    @14
    @25
    simp12
    #
    @4
    @6
    @8
    @13
    @25
    simp22
    #
    cK
    @39
    c.x
    cU
    cD
    cW
    @0
    @7
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.k
    @47
    lssvscl
    syl22anc
    @10
    @12
    @6
    @8
    @4
    @25
    simp23l
    #
    c.pl
    @39
    cU
    cW
    @32
    @9
    lshpkrlem.a
    @47
    lssvacl
    syl22anc
    @26
    @21
    c.x
    cD
    cK
    cN
    cV
    cW
    cZ
    lshpkrlem.v
    lshpkrlem.t
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.n
    @46
    @26
    wph
    @20
    cV
    wcel
    #
    @21
    cK
    wcel
    @43
    @26
    @41
    @19
    cV
    wcel
    #
    @6
    @60
    @46
    @26
    @41
    @1
    @3
    @61
    @46
    @57
    wph
    @1
    @3
    @14
    @25
    simp13
    #
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
    @4
    @6
    @8
    @13
    @25
    simp21
    #
    c.pl
    cV
    cW
    @19
    @5
    lshpkrlem.v
    lshpkrlem.a
    lmodvacl
    syl3anc
    wph
    @60
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
    @20
    c.0
    cZ
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    wph
    @42
    @60
    lshpkrlem.w
    adantr
    wph
    cU
    cH
    wcel
    #
    @60
    lshpkrlem.u
    adantr
    wph
    @53
    @60
    lshpkrlem.z
    adantr
    wph
    @60
    simpr
    wph
    cU
    @34
    c.po
    co
    cV
    wceq
    #
    @60
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
    @54
    lspsneli
    @26
    @30
    c.x
    cD
    cK
    cN
    cV
    cW
    cZ
    lshpkrlem.v
    lshpkrlem.t
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.n
    @46
    @26
    @41
    @28
    cK
    wcel
    #
    @17
    cK
    wcel
    #
    @30
    cK
    wcel
    @46
    @26
    @41
    @1
    @15
    cK
    wcel
    #
    @67
    @46
    @57
    @26
    wph
    @3
    @69
    @43
    @62
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
    @42
    @3
    lshpkrlem.w
    adantr
    wph
    @64
    @3
    lshpkrlem.u
    adantr
    wph
    @53
    @3
    lshpkrlem.z
    adantr
    wph
    @3
    simpr
    wph
    @65
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
    @27
    cD
    cK
    cW
    @0
    @15
    lshpkrlem.d
    lshpkrlem.k
    @27
    eqid
    lmodmcl
    syl3anc
    @26
    wph
    @6
    @68
    @43
    @63
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
    @42
    @6
    lshpkrlem.w
    adantr
    wph
    @64
    @6
    lshpkrlem.u
    adantr
    wph
    @53
    @6
    lshpkrlem.z
    adantr
    wph
    @6
    simpr
    wph
    @65
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
    @29
    cD
    cK
    cW
    @28
    @17
    lshpkrlem.d
    lshpkrlem.k
    @29
    eqid
    lmodacl
    syl3anc
    #
    @54
    lspsneli
    @26
    @20
    @23
    @33
    @31
    c.pl
    co
    #
    @4
    @14
    @16
    @18
    @24
    simp33
    @26
    @4
    @6
    @7
    cV
    wcel
    #
    @9
    cV
    wcel
    #
    @16
    @18
    @20
    @71
    wceq
    @4
    @14
    @25
    simp1
    @63
    @26
    @49
    @8
    @72
    @51
    @58
    @39
    cU
    cV
    cW
    @7
    lshpkrlem.v
    @47
    lssel
    syl2anc
    @26
    @49
    @10
    @73
    @51
    @59
    @39
    cU
    cV
    cW
    @9
    lshpkrlem.v
    @47
    lssel
    syl2anc
    @4
    @14
    @16
    @18
    @24
    simp31
    @4
    @14
    @16
    @18
    @24
    simp32
    wph
    vx
    vy
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
    cX
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
    lshpkrlem.x
    lshpkrlem.e
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpkrlem.o
    lshpkrlem.g
    lshpkrlem4
    syl132anc
    eqtr3d
    subgdisj2
    @26
    @21
    @30
    c.x
    cD
    cK
    cV
    cW
    cZ
    @35
    lshpkrlem.v
    lshpkrlem.t
    lshpkrlem.d
    lshpkrlem.k
    @37
    @44
    @66
    @70
    @54
    @26
    wph
    cZ
    @35
    wne
    @43
    wph
    c.po
    cU
    cH
    cN
    cV
    cW
    cZ
    @35
    lshpkrlem.v
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    @37
    @50
    lshpkrlem.u
    lshpkrlem.z
    lshpkrlem.e
    lshpne0
    syl
    lvecvscan2
    mpbid
end
