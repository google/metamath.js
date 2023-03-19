include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "clmod.mm"
include "wcel.mm"
include "cabl.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodabl.mm"
include "eldifad.mm"
include "ablsubsub4.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "wss.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "lspsntrim.mm"
include "eqsstr3d.mm"
include "ablsub32.mm"
include "eqtrd.mm"
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
include "baerlem5alem1.mm"
include "lmodvacl.mm"
include "lspsneli.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "impd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem baerlem5alem2
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


  assert |- ( ph -> ( N ` { ( X .- ( Y .+ Z ) ) } ) = ( ( ( N ` { ( X .- Y ) } ) .(+) ( N ` { Z } ) ) i^i ( ( N ` { ( X .- Z ) } ) .(+) ( N ` { Y } ) ) ) )

  proof
    wph
    cX
    cY
    cZ
    c.pl
    co
    #
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cX
    cY
    c.mi
    co
    #
    csn
    cN
    cfv
    cZ
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cX
    cZ
    c.mi
    co
    #
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cin
    #
    wph
    @3
    @6
    @9
    wph
    @3
    @4
    cZ
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    @6
    wph
    @12
    @2
    cN
    wph
    @11
    @1
    wph
    cV
    c.pl
    cW
    c.mi
    cX
    cY
    cZ
    baerlem3.v
    baerlem3.p
    baerlem3.m
    wph
    cW
    clmod
    wcel
    #
    cW
    cabl
    wcel
    wph
    cW
    clvec
    wcel
    #
    @14
    baerlem3.w
    cW
    lveclmod
    syl
    #
    cW
    lmodabl
    syl
    #
    baerlem3.x
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
    @18
    baerlem3.z
    eldifad
    #
    ablsubsub4
    #
    sneqd
    fveq2d
    wph
    @14
    @4
    cV
    wcel
    #
    cZ
    cV
    wcel
    #
    @13
    @6
    wss
    @16
    wph
    @14
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @22
    @16
    baerlem3.x
    @19
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
    @20
    c.po
    c.mi
    cN
    cV
    cW
    @4
    cZ
    baerlem3.v
    baerlem3.m
    baerlem3.s
    baerlem3.n
    lspsntrim
    syl3anc
    eqsstr3d
    wph
    @3
    @7
    cY
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    @9
    wph
    @28
    @2
    cN
    wph
    @27
    @1
    wph
    @27
    @11
    @1
    wph
    cV
    cW
    c.mi
    cX
    cZ
    cY
    baerlem3.v
    baerlem3.m
    @17
    baerlem3.x
    @20
    @19
    ablsub32
    @21
    eqtrd
    sneqd
    fveq2d
    wph
    @14
    @7
    cV
    wcel
    #
    @25
    @29
    @9
    wss
    @16
    wph
    @14
    @24
    @23
    @30
    @16
    baerlem3.x
    @20
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
    @19
    c.po
    c.mi
    cN
    cV
    cW
    @7
    cY
    baerlem3.v
    baerlem3.m
    baerlem3.s
    baerlem3.n
    lspsntrim
    syl3anc
    eqsstr3d
    ssind
    wph
    vj
    @10
    @3
    wph
    vj
    cv
    #
    @10
    wcel
    #
    @32
    va
    cv
    #
    @4
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
    @32
    vd
    cv
    #
    @7
    c.x
    co
    ve
    cv
    #
    cY
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
    @32
    @3
    wcel
    #
    @33
    @32
    @6
    wcel
    #
    @32
    @9
    wcel
    #
    wa
    wph
    @42
    @32
    @6
    @9
    elin
    wph
    @44
    @37
    @45
    @41
    wph
    c.pl
    c.po
    c.x
    @32
    va
    vb
    cR
    cB
    cN
    cV
    cW
    @4
    cZ
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.b
    baerlem3.t
    baerlem3.s
    baerlem3.n
    @16
    @26
    @20
    lsmspsn
    wph
    c.pl
    c.po
    c.x
    @32
    vd
    ve
    cR
    cB
    cN
    cV
    cW
    @7
    cY
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.b
    baerlem3.t
    baerlem3.s
    baerlem3.n
    @16
    @31
    @19
    lsmspsn
    anbi12d
    syl5bb
    wph
    @37
    @41
    @43
    wph
    @36
    @41
    @43
    wi
    #
    va
    vb
    cB
    cB
    wph
    @34
    cB
    wcel
    #
    @35
    cB
    wcel
    #
    wa
    #
    @36
    @46
    wph
    @49
    @36
    w3a
    #
    @40
    @43
    vd
    ve
    cB
    cB
    @50
    @38
    cB
    wcel
    #
    @39
    cB
    wcel
    #
    wa
    #
    @40
    @43
    @50
    @53
    @40
    w3a
    #
    @32
    @34
    @1
    c.x
    co
    @3
    @54
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
    @54
    wph
    @15
    wph
    @49
    @36
    @53
    @40
    simp11
    #
    baerlem3.w
    syl
    @54
    wph
    @24
    @55
    baerlem3.x
    syl
    @54
    wph
    cX
    cY
    cZ
    cpr
    cN
    cfv
    wcel
    wn
    @55
    baerlem3.c
    syl
    @54
    wph
    @8
    @5
    wne
    @55
    baerlem3.d
    syl
    @54
    wph
    cY
    cV
    @18
    cdif
    #
    wcel
    @55
    baerlem3.y
    syl
    @54
    wph
    cZ
    @56
    wcel
    @55
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
    @47
    @48
    wph
    @36
    @53
    @40
    simp12l
    #
    @47
    @48
    wph
    @36
    @53
    @40
    simp12r
    @50
    @51
    @52
    @40
    simp2l
    @50
    @51
    @52
    @40
    simp2r
    wph
    @49
    @36
    @53
    @40
    simp13
    @50
    @53
    @40
    simp3
    baerlem5alem1
    @54
    @34
    c.x
    cR
    cB
    cN
    cV
    cW
    @1
    baerlem3.v
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.n
    @54
    wph
    @14
    @55
    @16
    syl
    @57
    @54
    wph
    @1
    cV
    wcel
    #
    @55
    wph
    @14
    @24
    @0
    cV
    wcel
    #
    @58
    @16
    baerlem3.x
    wph
    @14
    @25
    @23
    @59
    @16
    @19
    @20
    c.pl
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.p
    lmodvacl
    syl3anc
    c.mi
    cV
    cW
    cX
    @0
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
