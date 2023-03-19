include "co.mm"
include "caddc.mm"
include "cmt.mm"
include "wcel.mm"
include "cr.mm"
include "cngp.mm"
include "cnlm.mm"
include "nlmngp.mm"
include "syl.mm"
include "ngpms.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "mscl.mm"
include "readdcld.mm"
include "rpred.mm"
include "cle.mm"
include "wbr.mm"
include "mstri.mm"
include "syl13anc.mm"
include "cfv.mm"
include "c1.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "nlmngp2.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "cc0.mm"
include "nmge0.mm"
include "ge0p1rpd.mm"
include "remulcld.mm"
include "rehalfcld.mm"
include "wceq.mm"
include "nlmdsdi.mm"
include "cxme.mm"
include "msxms.mm"
include "xmsge0.mm"
include "lep1d.mm"
include "lemul1ad.mm"
include "eqbrtrrd.mm"
include "clt.mm"
include "syl6breq.mm"
include "ltmuldiv2d.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "crp.mm"
include "rphalfcld.mm"
include "rpdivcld.mm"
include "syl5eqel.mm"
include "nlmdsdir.mm"
include "cmin.mm"
include "resubcld.mm"
include "csg.mm"
include "eqid.mm"
include "nm2dif.mm"
include "ngpdsr.mm"
include "breqtrrd.mm"
include "ltled.mm"
include "letrd.mm"
include "lesubadd2d.mm"
include "mpbid.mm"
include "lemul2ad.mm"
include "wb.mm"
include "0red.mm"
include "ltaddrpd.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "lt2halvesd.mm"

theorem nlmvscnlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  assume nlmvscn.f: |- F = ( Scalar ` W )
  assume nlmvscn.v: |- V = ( Base ` W )
  assume nlmvscn.k: |- K = ( Base ` F )
  assume nlmvscn.d: |- D = ( dist ` W )
  assume nlmvscn.e: |- E = ( dist ` F )
  assume nlmvscn.n: |- N = ( norm ` W )
  assume nlmvscn.a: |- A = ( norm ` F )
  assume nlmvscn.s: |- .x. = ( .s ` W )
  assume nlmvscn.t: |- T = ( ( R / 2 ) / ( ( A ` B ) + 1 ) )
  assume nlmvscn.u: |- U = ( ( R / 2 ) / ( ( N ` X ) + T ) )
  assume nlmvscn.w: |- ( ph -> W e. NrmMod )
  assume nlmvscn.r: |- ( ph -> R e. RR+ )
  assume nlmvscn.b: |- ( ph -> B e. K )
  assume nlmvscn.x: |- ( ph -> X e. V )
  assume nlmvscn.c: |- ( ph -> C e. K )
  assume nlmvscn.y: |- ( ph -> Y e. V )
  assume nlmvscn.1: |- ( ph -> ( B E C ) < U )
  assume nlmvscn.2: |- ( ph -> ( X D Y ) < T )


  assert |- ( ph -> ( ( B .x. X ) D ( C .x. Y ) ) < R )

  proof
    wph
    cB
    cX
    c.x
    co
    #
    cC
    cY
    c.x
    co
    #
    cD
    co
    #
    @0
    cB
    cY
    c.x
    co
    #
    cD
    co
    #
    @3
    @1
    cD
    co
    #
    caddc
    co
    #
    cR
    wph
    cW
    cmt
    wcel
    #
    @0
    cV
    wcel
    #
    @1
    cV
    wcel
    #
    @2
    cr
    wcel
    wph
    cW
    cngp
    wcel
    #
    @7
    wph
    cW
    cnlm
    wcel
    #
    @10
    nlmvscn.w
    cW
    nlmngp
    syl
    #
    cW
    ngpms
    syl
    #
    wph
    cW
    clmod
    wcel
    #
    cB
    cK
    wcel
    #
    cX
    cV
    wcel
    #
    @8
    wph
    @11
    @14
    nlmvscn.w
    cW
    nlmlmod
    syl
    #
    nlmvscn.b
    nlmvscn.x
    cB
    c.x
    cF
    cK
    cV
    cW
    cX
    nlmvscn.v
    nlmvscn.f
    nlmvscn.s
    nlmvscn.k
    lmodvscl
    syl3anc
    #
    wph
    @14
    cC
    cK
    wcel
    #
    cY
    cV
    wcel
    #
    @9
    @17
    nlmvscn.c
    nlmvscn.y
    cC
    c.x
    cF
    cK
    cV
    cW
    cY
    nlmvscn.v
    nlmvscn.f
    nlmvscn.s
    nlmvscn.k
    lmodvscl
    syl3anc
    #
    @0
    @1
    cD
    cW
    cV
    nlmvscn.v
    nlmvscn.d
    mscl
    syl3anc
    wph
    @4
    @5
    wph
    @7
    @8
    @3
    cV
    wcel
    #
    @4
    cr
    wcel
    @13
    @18
    wph
    @14
    @15
    @20
    @22
    @17
    nlmvscn.b
    nlmvscn.y
    cB
    c.x
    cF
    cK
    cV
    cW
    cY
    nlmvscn.v
    nlmvscn.f
    nlmvscn.s
    nlmvscn.k
    lmodvscl
    syl3anc
    #
    @0
    @3
    cD
    cW
    cV
    nlmvscn.v
    nlmvscn.d
    mscl
    syl3anc
    #
    wph
    @7
    @22
    @9
    @5
    cr
    wcel
    @13
    @23
    @21
    @3
    @1
    cD
    cW
    cV
    nlmvscn.v
    nlmvscn.d
    mscl
    syl3anc
    #
    readdcld
    wph
    cR
    nlmvscn.r
    rpred
    #
    wph
    @7
    @8
    @9
    @22
    @2
    @6
    cle
    wbr
    @13
    @18
    @21
    @23
    @0
    @1
    @3
    cD
    cW
    cV
    nlmvscn.v
    nlmvscn.d
    mstri
    syl13anc
    wph
    @4
    @5
    cR
    @24
    @25
    @26
    wph
    @4
    cB
    cA
    cfv
    #
    c1
    caddc
    co
    #
    cX
    cY
    cD
    co
    #
    cmul
    co
    #
    cR
    c2
    cdiv
    co
    #
    @24
    wph
    @28
    @29
    wph
    @28
    wph
    @27
    wph
    cF
    cngp
    wcel
    #
    @15
    @27
    cr
    wcel
    wph
    @11
    @32
    nlmvscn.w
    cF
    cW
    nlmvscn.f
    nlmngp2
    syl
    #
    nlmvscn.b
    cB
    cF
    cA
    cK
    nlmvscn.k
    nlmvscn.a
    nmcl
    syl2anc
    #
    wph
    @32
    @15
    cc0
    @27
    cle
    wbr
    @33
    nlmvscn.b
    cB
    cF
    cA
    cK
    nlmvscn.k
    nlmvscn.a
    nmge0
    syl2anc
    ge0p1rpd
    #
    rpred
    #
    wph
    @7
    @16
    @20
    @29
    cr
    wcel
    @13
    nlmvscn.x
    nlmvscn.y
    cX
    cY
    cD
    cW
    cV
    nlmvscn.v
    nlmvscn.d
    mscl
    syl3anc
    #
    remulcld
    wph
    cR
    @26
    rehalfcld
    #
    wph
    @27
    @29
    cmul
    co
    #
    @4
    @30
    cle
    wph
    @11
    @15
    @16
    @20
    @39
    @4
    wceq
    nlmvscn.w
    nlmvscn.b
    nlmvscn.x
    nlmvscn.y
    cA
    cD
    c.x
    cF
    cK
    cV
    cW
    cB
    cX
    cY
    nlmvscn.v
    nlmvscn.s
    nlmvscn.f
    nlmvscn.k
    nlmvscn.d
    nlmvscn.a
    nlmdsdi
    syl13anc
    wph
    @27
    @28
    @29
    @34
    @36
    @37
    wph
    cW
    cxme
    wcel
    #
    @16
    @20
    cc0
    @29
    cle
    wbr
    wph
    @7
    @40
    @13
    cW
    msxms
    syl
    nlmvscn.x
    nlmvscn.y
    cX
    cY
    cD
    cW
    cV
    nlmvscn.v
    nlmvscn.d
    xmsge0
    syl3anc
    wph
    @27
    @34
    lep1d
    lemul1ad
    eqbrtrrd
    wph
    @30
    @31
    clt
    wbr
    @29
    @31
    @28
    cdiv
    co
    #
    clt
    wbr
    wph
    @29
    cT
    @41
    clt
    nlmvscn.2
    nlmvscn.t
    syl6breq
    wph
    @29
    @31
    @28
    @37
    @38
    @35
    ltmuldiv2d
    mpbird
    lelttrd
    wph
    @5
    cB
    cC
    cE
    co
    #
    cX
    cN
    cfv
    #
    cT
    caddc
    co
    #
    cmul
    co
    #
    @31
    @25
    wph
    @42
    @44
    wph
    cF
    cmt
    wcel
    #
    @15
    @19
    @42
    cr
    wcel
    #
    wph
    @32
    @46
    @33
    cF
    ngpms
    syl
    #
    nlmvscn.b
    nlmvscn.c
    cB
    cC
    cE
    cF
    cK
    nlmvscn.k
    nlmvscn.e
    mscl
    syl3anc
    #
    wph
    @43
    cT
    wph
    @10
    @16
    @43
    cr
    wcel
    @12
    nlmvscn.x
    cX
    cW
    cN
    cV
    nlmvscn.v
    nlmvscn.n
    nmcl
    syl2anc
    #
    wph
    cT
    wph
    cT
    @41
    crp
    nlmvscn.t
    wph
    @31
    @28
    wph
    cR
    nlmvscn.r
    rphalfcld
    @35
    rpdivcld
    syl5eqel
    #
    rpred
    #
    readdcld
    #
    remulcld
    @38
    wph
    @42
    cY
    cN
    cfv
    #
    cmul
    co
    #
    @5
    @45
    cle
    wph
    @11
    @15
    @19
    @20
    @55
    @5
    wceq
    nlmvscn.w
    nlmvscn.b
    nlmvscn.c
    nlmvscn.y
    cD
    c.x
    cE
    cF
    cK
    cN
    cV
    cW
    cB
    cC
    cY
    nlmvscn.v
    nlmvscn.s
    nlmvscn.f
    nlmvscn.k
    nlmvscn.d
    nlmvscn.n
    nlmvscn.e
    nlmdsdir
    syl13anc
    wph
    @54
    @44
    @42
    wph
    @10
    @20
    @54
    cr
    wcel
    @12
    nlmvscn.y
    cY
    cW
    cN
    cV
    nlmvscn.v
    nlmvscn.n
    nmcl
    syl2anc
    #
    @53
    @49
    wph
    cF
    cxme
    wcel
    #
    @15
    @19
    cc0
    @42
    cle
    wbr
    wph
    @46
    @57
    @48
    cF
    msxms
    syl
    nlmvscn.b
    nlmvscn.c
    cB
    cC
    cE
    cF
    cK
    nlmvscn.k
    nlmvscn.e
    xmsge0
    syl3anc
    wph
    @54
    @43
    cmin
    co
    #
    cT
    cle
    wbr
    @54
    @44
    cle
    wbr
    wph
    @58
    @29
    cT
    wph
    @54
    @43
    @56
    @50
    resubcld
    @37
    @52
    wph
    @58
    cY
    cX
    cW
    csg
    cfv
    #
    co
    cN
    cfv
    #
    @29
    cle
    wph
    @10
    @20
    @16
    @58
    @60
    cle
    wbr
    @12
    nlmvscn.y
    nlmvscn.x
    cY
    cX
    cW
    @59
    cN
    cV
    nlmvscn.v
    nlmvscn.n
    @59
    eqid
    #
    nm2dif
    syl3anc
    wph
    @10
    @16
    @20
    @29
    @60
    wceq
    @12
    nlmvscn.x
    nlmvscn.y
    cX
    cY
    cD
    cW
    @59
    cN
    cV
    nlmvscn.n
    nlmvscn.v
    @61
    nlmvscn.d
    ngpdsr
    syl3anc
    breqtrrd
    wph
    @29
    cT
    @37
    @52
    nlmvscn.2
    ltled
    letrd
    wph
    @54
    @43
    cT
    @56
    @50
    @52
    lesubadd2d
    mpbid
    lemul2ad
    eqbrtrrd
    wph
    @45
    @31
    clt
    wbr
    #
    @42
    @31
    @44
    cdiv
    co
    #
    clt
    wbr
    #
    wph
    @42
    cU
    @63
    clt
    nlmvscn.1
    nlmvscn.u
    syl6breq
    wph
    @47
    @31
    cr
    wcel
    @44
    cr
    wcel
    cc0
    @44
    clt
    wbr
    @62
    @64
    wb
    @49
    @38
    @53
    wph
    cc0
    @43
    @44
    wph
    0red
    @50
    @53
    wph
    @10
    @16
    cc0
    @43
    cle
    wbr
    @12
    nlmvscn.x
    cX
    cW
    cN
    cV
    nlmvscn.v
    nlmvscn.n
    nmge0
    syl2anc
    wph
    @43
    cT
    @50
    @51
    ltaddrpd
    lelttrd
    @42
    @31
    @44
    ltmuldiv
    syl112anc
    mpbird
    lelttrd
    lt2halvesd
    lelttrd
end
