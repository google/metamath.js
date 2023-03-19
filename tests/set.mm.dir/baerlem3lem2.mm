include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eldifad.mm"
include "lspsntrim.mm"
include "syl3anc.mm"
include "lspsnsub.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablnnncan1.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "lmodvsubcl.mm"
include "eqsstrd.mm"
include "ssind.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "elin.mm"
include "lsmspsn.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "wi.mm"
include "w3a.mm"
include "simp11.mm"
include "cpr.mm"
include "wn.mm"
include "wne.mm"
include "cdif.mm"
include "simp12l.mm"
include "simp12r.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp13.mm"
include "simp3.mm"
include "baerlem3lem1.mm"
include "lspsneli.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "impd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem baerlem3lem2
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vj: setvar j
  assume baerlem3.v: |- V = ( Base ` W )
  assume baerlem3.m: |- .- = ( -g ` W )
  assume baerlem3.o: |- .0. = ( 0g ` W )
  assume baerlem3.s: |- .(+) = ( LSSum ` W )
  assume baerlem3.n: |- N = ( LSpan ` W )
  assume baerlem3.w: |- ( ph -> W e. LVec )
  assume baerlem3.x: |- ( ph -> X e. V )
  assume baerlem3.c: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume baerlem3.d: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume baerlem3.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume baerlem3.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume baerlem3.p: |- .+ = ( +g ` W )
  assume baerlem3.t: |- .x. = ( .s ` W )
  assume baerlem3.r: |- R = ( Scalar ` W )
  assume baerlem3.b: |- B = ( Base ` R )
  assume baerlem3.a: |- .+^ = ( +g ` R )
  assume baerlem3.l: |- L = ( -g ` R )
  assume baerlem3.q: |- Q = ( 0g ` R )
  assume baerlem3.i: |- I = ( invg ` R )


  assert |- ( ph -> ( N ` { ( Y .- Z ) } ) = ( ( ( N ` { Y } ) .(+) ( N ` { Z } ) ) i^i ( ( N ` { ( X .- Y ) } ) .(+) ( N ` { ( X .- Z ) } ) ) ) )

  proof
    wph
    cY
    cZ
    c.mi
    co
    #
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cZ
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cX
    cY
    c.mi
    co
    #
    csn
    cN
    cfv
    cX
    cZ
    c.mi
    co
    #
    csn
    cN
    cfv
    c.po
    co
    #
    cin
    #
    wph
    @1
    @4
    @7
    wph
    cW
    clmod
    wcel
    #
    cY
    cV
    wcel
    #
    cZ
    cV
    wcel
    #
    @1
    @4
    wss
    wph
    cW
    clvec
    wcel
    #
    @9
    baerlem3.w
    cW
    lveclmod
    syl
    #
    wph
    cY
    cV
    c.0
    csn
    #
    baerlem3.y
    eldifad
    #
    wph
    cZ
    cV
    @14
    baerlem3.z
    eldifad
    #
    c.po
    c.mi
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.m
    baerlem3.s
    baerlem3.n
    lspsntrim
    syl3anc
    wph
    @1
    @5
    @6
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    @7
    wph
    @1
    cZ
    cY
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    @19
    wph
    c.mi
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.m
    baerlem3.n
    @13
    @15
    @16
    lspsnsub
    wph
    @18
    @21
    cN
    wph
    @17
    @20
    wph
    cV
    cW
    c.mi
    cX
    cY
    cZ
    baerlem3.v
    baerlem3.m
    wph
    @9
    cW
    cabl
    wcel
    @13
    cW
    lmodabl
    syl
    baerlem3.x
    @15
    @16
    ablnnncan1
    sneqd
    fveq2d
    eqtr4d
    wph
    @9
    @5
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    @19
    @7
    wss
    @13
    wph
    @9
    cX
    cV
    wcel
    #
    @10
    @22
    @13
    baerlem3.x
    @15
    c.mi
    cV
    cW
    cX
    cY
    baerlem3.v
    baerlem3.m
    lmodvsubcl
    syl3anc
    #
    wph
    @9
    @24
    @11
    @23
    @13
    baerlem3.x
    @16
    c.mi
    cV
    cW
    cX
    cZ
    baerlem3.v
    baerlem3.m
    lmodvsubcl
    syl3anc
    #
    c.po
    c.mi
    cN
    cV
    cW
    @5
    @6
    baerlem3.v
    baerlem3.m
    baerlem3.s
    baerlem3.n
    lspsntrim
    syl3anc
    eqsstrd
    ssind
    wph
    vj
    @8
    @1
    wph
    vj
    cv
    #
    @8
    wcel
    #
    @27
    va
    cv
    #
    cY
    c.x
    co
    vb
    cv
    #
    cZ
    c.x
    co
    c.pl
    co
    wceq
    #
    vb
    cB
    wrex
    va
    cB
    wrex
    #
    @27
    vd
    cv
    #
    @5
    c.x
    co
    ve
    cv
    #
    @6
    c.x
    co
    c.pl
    co
    wceq
    #
    ve
    cB
    wrex
    vd
    cB
    wrex
    #
    wa
    #
    @27
    @1
    wcel
    #
    @28
    @27
    @4
    wcel
    #
    @27
    @7
    wcel
    #
    wa
    wph
    @37
    @27
    @4
    @7
    elin
    wph
    @39
    @32
    @40
    @36
    wph
    c.pl
    c.po
    c.x
    @27
    va
    vb
    cR
    cB
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.b
    baerlem3.t
    baerlem3.s
    baerlem3.n
    @13
    @15
    @16
    lsmspsn
    wph
    c.pl
    c.po
    c.x
    @27
    vd
    ve
    cR
    cB
    cN
    cV
    cW
    @5
    @6
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.b
    baerlem3.t
    baerlem3.s
    baerlem3.n
    @13
    @25
    @26
    lsmspsn
    anbi12d
    syl5bb
    wph
    @32
    @36
    @38
    wph
    @31
    @36
    @38
    wi
    #
    va
    vb
    cB
    cB
    wph
    @29
    cB
    wcel
    #
    @30
    cB
    wcel
    #
    wa
    #
    @31
    @41
    wph
    @44
    @31
    w3a
    #
    @35
    @38
    vd
    ve
    cB
    cB
    @45
    @33
    cB
    wcel
    #
    @34
    cB
    wcel
    #
    wa
    #
    @35
    @38
    @45
    @48
    @35
    w3a
    #
    @27
    @29
    @0
    c.x
    co
    @1
    @49
    cB
    c.pl
    c.pd
    c.po
    cQ
    cR
    c.x
    ve
    vj
    cI
    cL
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    va
    vb
    vd
    baerlem3.v
    baerlem3.m
    baerlem3.o
    baerlem3.s
    baerlem3.n
    @49
    wph
    @12
    wph
    @44
    @31
    @48
    @35
    simp11
    #
    baerlem3.w
    syl
    @49
    wph
    @24
    @50
    baerlem3.x
    syl
    @49
    wph
    cX
    cY
    cZ
    cpr
    cN
    cfv
    wcel
    wn
    @50
    baerlem3.c
    syl
    @49
    wph
    @2
    @3
    wne
    @50
    baerlem3.d
    syl
    @49
    wph
    cY
    cV
    @14
    cdif
    #
    wcel
    @50
    baerlem3.y
    syl
    @49
    wph
    cZ
    @51
    wcel
    @50
    baerlem3.z
    syl
    baerlem3.p
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.a
    baerlem3.l
    baerlem3.q
    baerlem3.i
    @42
    @43
    wph
    @31
    @48
    @35
    simp12l
    #
    @42
    @43
    wph
    @31
    @48
    @35
    simp12r
    @45
    @46
    @47
    @35
    simp2l
    @45
    @46
    @47
    @35
    simp2r
    wph
    @44
    @31
    @48
    @35
    simp13
    @45
    @48
    @35
    simp3
    baerlem3lem1
    @49
    @29
    c.x
    cR
    cB
    cN
    cV
    cW
    @0
    baerlem3.v
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.n
    @49
    wph
    @9
    @50
    @13
    syl
    @52
    @49
    wph
    @0
    cV
    wcel
    #
    @50
    wph
    @9
    @10
    @11
    @53
    @13
    @15
    @16
    c.mi
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.m
    lmodvsubcl
    syl3anc
    syl
    lspsneli
    eqeltrd
    3exp
    rexlimdvv
    3exp
    rexlimdvv
    impd
    sylbid
    ssrdv
    eqssd
end
