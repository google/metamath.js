include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "csn.mm"
include "cfv.mm"
include "hdmapglem7a.mm"
include "wi.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "crg.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodring.mm"
include "syl.mm"
include "simplrr.mm"
include "simprr.mm"
include "hgmapcl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "wss.mm"
include "c0g.mm"
include "cbs.mm"
include "cltrn.mm"
include "eqid.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "snssd.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "simplrl.mm"
include "sseldd.mm"
include "simprl.mm"
include "hdmapipcl.mm"
include "hgmapadd.mm"
include "hgmapmul.mm"
include "hgmapvv.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "csg.mm"
include "hdmapglem5.mm"
include "oveq12d.mm"
include "hdmapglem7b.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "3adantl3.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp13.mm"
include "fveq12d.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mp2d.mm"

theorem hdmapglem7
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let c.po: class .(+)
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vk: setvar k
  let vl: setvar l
  let vu: setvar u
  let vv: setvar v
  assume hdmapglem7.h: |- H = ( LHyp ` K )
  assume hdmapglem7.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapglem7.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapglem7.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapglem7.v: |- V = ( Base ` U )
  assume hdmapglem7.p: |- .+ = ( +g ` U )
  assume hdmapglem7.q: |- .x. = ( .s ` U )
  assume hdmapglem7.r: |- R = ( Scalar ` U )
  assume hdmapglem7.b: |- B = ( Base ` R )
  assume hdmapglem7.a: |- .(+) = ( LSSum ` U )
  assume hdmapglem7.n: |- N = ( LSpan ` U )
  assume hdmapglem7.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapglem7.x: |- ( ph -> X e. V )
  assume hdmapglem7.t: |- .X. = ( .r ` R )
  assume hdmapglem7.z: |- .0. = ( 0g ` R )
  assume hdmapglem7.c: |- .+b = ( +g ` R )
  assume hdmapglem7.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapglem7.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapglem7.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( G ` ( ( S ` Y ) ` X ) ) = ( ( S ` X ) ` Y ) )

  proof
    wph
    cX
    vk
    cv
    #
    cE
    c.x
    co
    vu
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vk
    cB
    wrex
    vu
    cE
    csn
    #
    cO
    cfv
    #
    wrex
    cY
    vl
    cv
    #
    cE
    c.x
    co
    vv
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vl
    cB
    wrex
    vv
    @5
    wrex
    #
    cX
    cY
    cS
    cfv
    #
    cfv
    #
    cG
    cfv
    #
    cY
    cX
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    wph
    vu
    cB
    c.pl
    c.po
    cR
    c.x
    cU
    vk
    cE
    cH
    cK
    cN
    cO
    cV
    cW
    cX
    hdmapglem7.h
    hdmapglem7.e
    hdmapglem7.o
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.p
    hdmapglem7.q
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.a
    hdmapglem7.n
    hdmapglem7.k
    hdmapglem7.x
    hdmapglem7a
    wph
    vv
    cB
    c.pl
    c.po
    cR
    c.x
    cU
    vl
    cE
    cH
    cK
    cN
    cO
    cV
    cW
    cY
    hdmapglem7.h
    hdmapglem7.e
    hdmapglem7.o
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.p
    hdmapglem7.q
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.a
    hdmapglem7.n
    hdmapglem7.k
    hdmapglem7.y
    hdmapglem7a
    wph
    @3
    @10
    @16
    wi
    #
    vu
    vk
    @5
    cB
    wph
    @1
    @5
    wcel
    #
    @0
    cB
    wcel
    #
    wa
    #
    @3
    @17
    wph
    @20
    @3
    w3a
    #
    @9
    @16
    vv
    vl
    @5
    cB
    @21
    @7
    @5
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    @9
    @16
    @21
    @24
    @9
    w3a
    #
    @2
    @8
    cS
    cfv
    #
    cfv
    #
    cG
    cfv
    #
    @8
    @2
    cS
    cfv
    #
    cfv
    #
    @13
    @15
    @21
    @24
    @28
    @30
    wceq
    #
    @9
    wph
    @20
    @24
    @31
    @3
    wph
    @20
    wa
    #
    @24
    wa
    #
    @0
    @6
    cG
    cfv
    #
    c.xp
    co
    #
    @1
    @7
    cS
    cfv
    cfv
    #
    c.pb
    co
    #
    cG
    cfv
    #
    @6
    @0
    cG
    cfv
    #
    c.xp
    co
    #
    @7
    @1
    cS
    cfv
    cfv
    #
    c.pb
    co
    #
    @28
    @30
    @33
    @38
    @35
    cG
    cfv
    #
    @36
    cG
    cfv
    #
    c.pb
    co
    @42
    @33
    cB
    c.pb
    cR
    cU
    cG
    cH
    cK
    cW
    @35
    @36
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.c
    hdmapglem7.g
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @20
    @24
    hdmapglem7.k
    ad2antrr
    #
    @33
    cR
    crg
    wcel
    #
    @19
    @34
    cB
    wcel
    @35
    cB
    wcel
    wph
    @47
    @20
    @24
    wph
    cU
    clmod
    wcel
    @47
    wph
    cU
    cH
    cK
    cW
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.k
    dvhlmod
    cR
    cU
    hdmapglem7.r
    lmodring
    syl
    ad2antrr
    wph
    @18
    @19
    @24
    simplrr
    #
    @33
    cB
    cR
    cU
    @6
    cG
    cH
    cK
    cW
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.g
    @46
    @32
    @22
    @23
    simprr
    #
    hgmapcl
    #
    cB
    cR
    c.xp
    @0
    @34
    hdmapglem7.b
    hdmapglem7.t
    ringcl
    syl3anc
    @33
    cB
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    @1
    @7
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.s
    @46
    @33
    @5
    cV
    @1
    wph
    @5
    cV
    wss
    #
    @20
    @24
    wph
    @45
    @4
    cV
    wss
    @51
    hdmapglem7.k
    wph
    cE
    cV
    wph
    cE
    cV
    cU
    c0g
    cfv
    #
    csn
    wph
    cK
    cbs
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cE
    cH
    cK
    cV
    cW
    @52
    hdmapglem7.h
    @53
    eqid
    @54
    eqid
    hdmapglem7.u
    hdmapglem7.v
    @52
    eqid
    hdmapglem7.e
    hdmapglem7.k
    dvheveccl
    eldifad
    snssd
    cU
    cH
    cK
    cO
    cV
    cW
    @4
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.o
    dochssv
    syl2anc
    ad2antrr
    #
    wph
    @18
    @19
    @24
    simplrl
    #
    sseldd
    @33
    @5
    cV
    @7
    @55
    @32
    @22
    @23
    simprl
    #
    sseldd
    hdmapipcl
    hgmapadd
    @33
    @43
    @40
    @44
    @41
    c.pb
    @33
    @43
    @34
    cG
    cfv
    #
    @39
    c.xp
    co
    @40
    @33
    cB
    cR
    c.xp
    cU
    cG
    cH
    cK
    cW
    @0
    @34
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.t
    hdmapglem7.g
    @46
    @48
    @50
    hgmapmul
    @33
    @58
    @6
    @39
    c.xp
    @33
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    @6
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.g
    @46
    @49
    hgmapvv
    oveq1d
    eqtrd
    @33
    cB
    @1
    @7
    c.pl
    cR
    cS
    c.x
    c.xp
    cU
    cE
    cG
    cH
    @0
    @0
    cK
    cU
    csg
    cfv
    #
    cO
    cV
    cW
    c.0
    hdmapglem7.h
    hdmapglem7.e
    hdmapglem7.o
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.p
    @59
    eqid
    hdmapglem7.q
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.t
    hdmapglem7.z
    hdmapglem7.s
    hdmapglem7.g
    @46
    @56
    @57
    @48
    @48
    hdmapglem5
    oveq12d
    eqtrd
    @33
    @27
    @37
    cG
    @33
    vv
    vu
    cB
    c.pl
    c.pb
    c.po
    cR
    cS
    c.x
    c.xp
    cU
    vl
    vk
    cE
    cG
    cH
    cK
    cN
    cO
    cV
    cW
    cX
    c.0
    hdmapglem7.h
    hdmapglem7.e
    hdmapglem7.o
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.p
    hdmapglem7.q
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.a
    hdmapglem7.n
    @46
    wph
    cX
    cV
    wcel
    @20
    @24
    hdmapglem7.x
    ad2antrr
    #
    hdmapglem7.t
    hdmapglem7.z
    hdmapglem7.c
    hdmapglem7.s
    hdmapglem7.g
    @57
    @56
    @49
    @48
    hdmapglem7b
    fveq2d
    @33
    vu
    vv
    cB
    c.pl
    c.pb
    c.po
    cR
    cS
    c.x
    c.xp
    cU
    vk
    vl
    cE
    cG
    cH
    cK
    cN
    cO
    cV
    cW
    cX
    c.0
    hdmapglem7.h
    hdmapglem7.e
    hdmapglem7.o
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.p
    hdmapglem7.q
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.a
    hdmapglem7.n
    @46
    @60
    hdmapglem7.t
    hdmapglem7.z
    hdmapglem7.c
    hdmapglem7.s
    hdmapglem7.g
    @56
    @57
    @48
    @49
    hdmapglem7b
    3eqtr4d
    3adantl3
    3adant3
    @25
    @12
    @27
    cG
    @25
    cX
    @2
    @11
    @26
    @25
    cY
    @8
    cS
    @21
    @24
    @9
    simp3
    #
    fveq2d
    wph
    @20
    @3
    @24
    @9
    simp13
    #
    fveq12d
    fveq2d
    @25
    cY
    @8
    @14
    @29
    @25
    cX
    @2
    cS
    @62
    fveq2d
    @61
    fveq12d
    3eqtr4d
    3exp
    rexlimdvv
    3exp
    rexlimdvv
    mp2d
end
