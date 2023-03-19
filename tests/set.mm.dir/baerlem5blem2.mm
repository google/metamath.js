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
include "lspsntri.mm"
include "syl3anc.mm"
include "lmodvacl.mm"
include "lmodvsubcl.mm"
include "lspsnsub.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablnncan.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "lspsntrim.mm"
include "eqsstr3d.mm"
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
include "baerlem5blem1.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "ringgrp.mm"
include "4syl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lspsneli.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "impd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem baerlem5blem2
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


  assert |- ( ph -> ( N ` { ( Y .+ Z ) } ) = ( ( ( N ` { Y } ) .(+) ( N ` { Z } ) ) i^i ( ( N ` { ( X .- ( Y .+ Z ) ) } ) .(+) ( N ` { X } ) ) ) )

  proof
    wph
    cY
    cZ
    c.pl
    co
    #
    csn
    #
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
    @0
    c.mi
    co
    #
    csn
    cN
    cfv
    cX
    csn
    cN
    cfv
    c.po
    co
    #
    cin
    #
    wph
    @2
    @5
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
    @2
    @5
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
    c.pl
    c.po
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.p
    baerlem3.n
    baerlem3.s
    lspsntri
    syl3anc
    wph
    @2
    @6
    cX
    c.mi
    co
    csn
    cN
    cfv
    #
    @7
    wph
    @17
    cX
    @6
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    @2
    wph
    c.mi
    cN
    cV
    cW
    @6
    cX
    baerlem3.v
    baerlem3.m
    baerlem3.n
    @13
    wph
    @9
    cX
    cV
    wcel
    #
    @0
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    @13
    baerlem3.x
    wph
    @9
    @10
    @11
    @21
    @13
    @15
    @16
    c.pl
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.p
    lmodvacl
    syl3anc
    #
    c.mi
    cV
    cW
    cX
    @0
    baerlem3.v
    baerlem3.m
    lmodvsubcl
    syl3anc
    #
    baerlem3.x
    lspsnsub
    wph
    @19
    @1
    cN
    wph
    @18
    @0
    wph
    cV
    cW
    c.mi
    cX
    @0
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
    @23
    ablnncan
    sneqd
    fveq2d
    eqtrd
    wph
    @9
    @22
    @20
    @17
    @7
    wss
    @13
    @24
    baerlem3.x
    c.po
    c.mi
    cN
    cV
    cW
    @6
    cX
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
    @8
    @2
    wph
    vj
    cv
    #
    @8
    wcel
    #
    @25
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
    @25
    vd
    cv
    #
    @6
    c.x
    co
    ve
    cv
    #
    cX
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
    @25
    @2
    wcel
    #
    @26
    @25
    @5
    wcel
    #
    @25
    @7
    wcel
    #
    wa
    wph
    @35
    @25
    @5
    @7
    elin
    wph
    @37
    @30
    @38
    @34
    wph
    c.pl
    c.po
    c.x
    @25
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
    @25
    vd
    ve
    cR
    cB
    cN
    cV
    cW
    @6
    cX
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.b
    baerlem3.t
    baerlem3.s
    baerlem3.n
    @13
    @24
    baerlem3.x
    lsmspsn
    anbi12d
    syl5bb
    wph
    @30
    @34
    @36
    wph
    @29
    @34
    @36
    wi
    #
    va
    vb
    cB
    cB
    wph
    @27
    cB
    wcel
    #
    @28
    cB
    wcel
    #
    wa
    #
    @29
    @39
    wph
    @42
    @29
    w3a
    #
    @33
    @36
    vd
    ve
    cB
    cB
    @43
    @31
    cB
    wcel
    #
    @32
    cB
    wcel
    #
    wa
    #
    @33
    @36
    @43
    @46
    @33
    w3a
    #
    @25
    @31
    cI
    cfv
    #
    @0
    c.x
    co
    @2
    @47
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
    @47
    wph
    @12
    wph
    @42
    @29
    @46
    @33
    simp11
    #
    baerlem3.w
    syl
    @47
    wph
    @20
    @49
    baerlem3.x
    syl
    @47
    wph
    cX
    cY
    cZ
    cpr
    cN
    cfv
    wcel
    wn
    @49
    baerlem3.c
    syl
    @47
    wph
    @3
    @4
    wne
    @49
    baerlem3.d
    syl
    @47
    wph
    cY
    cV
    @14
    cdif
    #
    wcel
    @49
    baerlem3.y
    syl
    @47
    wph
    cZ
    @50
    wcel
    @49
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
    @40
    @41
    wph
    @29
    @46
    @33
    simp12l
    @40
    @41
    wph
    @29
    @46
    @33
    simp12r
    @43
    @44
    @45
    @33
    simp2l
    #
    @43
    @44
    @45
    @33
    simp2r
    wph
    @42
    @29
    @46
    @33
    simp13
    @43
    @46
    @33
    simp3
    baerlem5blem1
    @47
    @48
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
    @47
    wph
    @9
    @49
    @13
    syl
    @47
    cR
    cgrp
    wcel
    #
    @44
    @48
    cB
    wcel
    @47
    wph
    @9
    cR
    crg
    wcel
    @52
    @49
    @13
    cR
    cW
    baerlem3.r
    lmodring
    cR
    ringgrp
    4syl
    @51
    cB
    cR
    cI
    @31
    baerlem3.b
    baerlem3.i
    grpinvcl
    syl2anc
    @47
    wph
    @21
    @49
    @23
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
