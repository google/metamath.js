include "hlhilbase.mm"
include "hlhilplus.mm"
include "hlhilvsca.mm"
include "cip.mm"
include "cfv.mm"
include "wceq.mm"
include "a1i.mm"
include "hlhil0.mm"
include "csca.mm"
include "hlhilsbase2.mm"
include "hlhilsplus2.mm"
include "hlhilsmul2.mm"
include "hlhilnvl.mm"
include "hlhils0.mm"
include "hlhillvec.mm"
include "hlhilsrng.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "hlhilipval.mm"
include "hdmapipcl.mm"
include "eqeltrd.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "hdmapln1.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmodvacl.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "adantr.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "hdmapip0.mm"
include "bitrd.mm"
include "biimp3a.mm"
include "hdmapg.mm"
include "fveq2d.mm"
include "isphld.mm"

theorem hlhilphllem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.xi: class .,
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume hlhilphl.h: |- H = ( LHyp ` K )
  assume hlhilphllem.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilphl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilphllem.f: |- F = ( Scalar ` U )
  assume hlhilphllem.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilphllem.v: |- V = ( Base ` L )
  assume hlhilphllem.a: |- .+ = ( +g ` L )
  assume hlhilphllem.s: |- .x. = ( .s ` L )
  assume hlhilphllem.r: |- R = ( Scalar ` L )
  assume hlhilphllem.b: |- B = ( Base ` R )
  assume hlhilphllem.p: |- .+^ = ( +g ` R )
  assume hlhilphllem.t: |- .X. = ( .r ` R )
  assume hlhilphllem.q: |- Q = ( 0g ` R )
  assume hlhilphllem.z: |- .0. = ( 0g ` L )
  assume hlhilphllem.i: |- ., = ( .i ` U )
  assume hlhilphllem.j: |- J = ( ( HDMap ` K ) ` W )
  assume hlhilphllem.g: |- G = ( ( HGMap ` K ) ` W )
  assume hlhilphllem.e: |- E = ( x e. V , y e. V |-> ( ( J ` y ) ` x ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint V x
  disjoint V y
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint U x
  disjoint W x
  disjoint W y
  disjoint ph x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint B b
  disjoint c d
  disjoint B c
  disjoint B d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint a x
  disjoint a y
  disjoint V a
  disjoint b x
  disjoint b y
  disjoint V b
  disjoint c x
  disjoint c y
  disjoint V c
  disjoint d x
  disjoint d y
  disjoint V d
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  assert |- ( ph -> U e. PreHil )

  proof
    wph
    va
    vb
    vc
    c.pl
    c.pd
    c.x
    c.xp
    cF
    c.xi
    cG
    cB
    cQ
    cV
    cU
    c.0
    vd
    wph
    cU
    cH
    cK
    cL
    cV
    cW
    hlhilphl.h
    hlhilphllem.u
    hlhilphl.k
    hlhilphllem.l
    hlhilphllem.v
    hlhilbase
    wph
    c.pl
    cU
    cH
    cK
    cL
    cW
    hlhilphl.h
    hlhilphllem.u
    hlhilphl.k
    hlhilphllem.l
    hlhilphllem.a
    hlhilplus
    wph
    c.x
    cU
    cH
    cK
    cL
    cW
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.s
    hlhilphllem.u
    hlhilphl.k
    hlhilvsca
    c.xi
    cU
    cip
    cfv
    wceq
    wph
    hlhilphllem.i
    a1i
    wph
    cU
    cH
    cK
    cL
    cW
    c.0
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.u
    hlhilphl.k
    hlhilphllem.z
    hlhil0
    cF
    cU
    csca
    cfv
    wceq
    wph
    hlhilphllem.f
    a1i
    wph
    cB
    cF
    cR
    cU
    cH
    cK
    cL
    cW
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.r
    hlhilphllem.u
    hlhilphllem.f
    hlhilphl.k
    hlhilphllem.b
    hlhilsbase2
    wph
    c.pd
    cF
    cR
    cU
    cH
    cK
    cL
    cW
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.r
    hlhilphllem.u
    hlhilphllem.f
    hlhilphl.k
    hlhilphllem.p
    hlhilsplus2
    wph
    cF
    cR
    c.xp
    cU
    cH
    cK
    cL
    cW
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.r
    hlhilphllem.u
    hlhilphllem.f
    hlhilphl.k
    hlhilphllem.t
    hlhilsmul2
    wph
    cF
    cU
    cH
    cG
    cK
    cW
    hlhilphl.h
    hlhilphllem.u
    hlhilphllem.f
    hlhilphllem.g
    hlhilphl.k
    hlhilnvl
    wph
    cF
    cR
    cU
    cH
    cK
    cL
    cW
    cQ
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.r
    hlhilphllem.u
    hlhilphllem.f
    hlhilphl.k
    hlhilphllem.q
    hlhils0
    wph
    cU
    cH
    cK
    cW
    hlhilphl.h
    hlhilphllem.u
    hlhilphl.k
    hlhillvec
    wph
    cF
    cU
    cH
    cK
    cW
    hlhilphl.h
    hlhilphllem.u
    hlhilphl.k
    hlhilphllem.f
    hlhilsrng
    wph
    va
    cv
    #
    cV
    wcel
    #
    vb
    cv
    #
    cV
    wcel
    #
    w3a
    #
    @0
    @2
    c.xi
    co
    #
    @0
    @2
    cJ
    cfv
    cfv
    #
    cB
    @4
    cJ
    cU
    cH
    c.xi
    cK
    cL
    cV
    cW
    @0
    @2
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.j
    hlhilphllem.u
    wph
    @1
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @3
    hlhilphl.k
    3ad2ant1
    #
    hlhilphllem.i
    wph
    @1
    @3
    simp2
    #
    wph
    @1
    @3
    simp3
    #
    hlhilipval
    #
    @4
    cB
    cR
    cJ
    cL
    cH
    cK
    cV
    cW
    @0
    @2
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.r
    hlhilphllem.b
    hlhilphllem.j
    @8
    @9
    @10
    hdmapipcl
    eqeltrd
    wph
    vd
    cv
    #
    cB
    wcel
    #
    @1
    @3
    vc
    cv
    #
    cV
    wcel
    #
    w3a
    #
    w3a
    #
    @12
    @0
    c.x
    co
    #
    @2
    c.pl
    co
    #
    @14
    cJ
    cfv
    #
    cfv
    @12
    @0
    @20
    cfv
    #
    c.xp
    co
    #
    @2
    @20
    cfv
    #
    c.pd
    co
    @19
    @14
    c.xi
    co
    @12
    @0
    @14
    c.xi
    co
    #
    c.xp
    co
    #
    @2
    @14
    c.xi
    co
    #
    c.pd
    co
    @17
    @12
    cB
    c.pl
    c.pd
    cR
    cJ
    c.x
    c.xp
    cL
    cH
    cK
    cV
    cW
    @0
    @2
    @14
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.a
    hlhilphllem.s
    hlhilphllem.r
    hlhilphllem.b
    hlhilphllem.p
    hlhilphllem.t
    hlhilphllem.j
    wph
    @13
    @7
    @16
    hlhilphl.k
    3ad2ant1
    #
    wph
    @13
    @1
    @3
    @15
    simp31
    #
    wph
    @13
    @1
    @3
    @15
    simp32
    #
    wph
    @13
    @1
    @3
    @15
    simp33
    #
    wph
    @13
    @16
    simp2
    #
    hdmapln1
    @17
    cJ
    cU
    cH
    c.xi
    cK
    cL
    cV
    cW
    @19
    @14
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.j
    hlhilphllem.u
    @27
    hlhilphllem.i
    @17
    cL
    clmod
    wcel
    #
    @18
    cV
    wcel
    #
    @3
    @19
    cV
    wcel
    wph
    @13
    @32
    @16
    wph
    cL
    cH
    cK
    cW
    hlhilphl.h
    hlhilphllem.l
    hlhilphl.k
    dvhlmod
    3ad2ant1
    #
    @17
    @32
    @13
    @1
    @33
    @34
    @31
    @28
    @12
    c.x
    cR
    cB
    cV
    cL
    @0
    hlhilphllem.v
    hlhilphllem.r
    hlhilphllem.s
    hlhilphllem.b
    lmodvscl
    syl3anc
    @29
    c.pl
    cV
    cL
    @18
    @2
    hlhilphllem.v
    hlhilphllem.a
    lmodvacl
    syl3anc
    @30
    hlhilipval
    @17
    @25
    @22
    @26
    @23
    c.pd
    @17
    @24
    @21
    @12
    c.xp
    @17
    cJ
    cU
    cH
    c.xi
    cK
    cL
    cV
    cW
    @0
    @14
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.j
    hlhilphllem.u
    @27
    hlhilphllem.i
    @28
    @30
    hlhilipval
    oveq2d
    @17
    cJ
    cU
    cH
    c.xi
    cK
    cL
    cV
    cW
    @2
    @14
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.j
    hlhilphllem.u
    @27
    hlhilphllem.i
    @29
    @30
    hlhilipval
    oveq12d
    3eqtr4d
    wph
    @1
    @0
    @0
    c.xi
    co
    #
    cQ
    wceq
    #
    @0
    c.0
    wceq
    #
    wph
    @1
    wa
    #
    @36
    @0
    @0
    cJ
    cfv
    #
    cfv
    #
    cQ
    wceq
    @37
    @38
    @35
    @40
    cQ
    @38
    cJ
    cU
    cH
    c.xi
    cK
    cL
    cV
    cW
    @0
    @0
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.j
    hlhilphllem.u
    wph
    @7
    @1
    hlhilphl.k
    adantr
    #
    hlhilphllem.i
    wph
    @1
    simpr
    #
    @42
    hlhilipval
    eqeq1d
    @38
    cR
    cJ
    cL
    cH
    cK
    cV
    cW
    @0
    c.0
    cQ
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.z
    hlhilphllem.r
    hlhilphllem.q
    hlhilphllem.j
    @41
    @42
    hdmapip0
    bitrd
    biimp3a
    @4
    @6
    cG
    cfv
    @2
    @39
    cfv
    @5
    cG
    cfv
    @2
    @0
    c.xi
    co
    @4
    cJ
    cL
    cG
    cH
    cK
    cV
    cW
    @0
    @2
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.j
    hlhilphllem.g
    @8
    @9
    @10
    hdmapg
    @4
    @5
    @6
    cG
    @11
    fveq2d
    @4
    cJ
    cU
    cH
    c.xi
    cK
    cL
    cV
    cW
    @2
    @0
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.j
    hlhilphllem.u
    @8
    hlhilphllem.i
    @10
    @9
    hlhilipval
    3eqtr4d
    isphld
end
