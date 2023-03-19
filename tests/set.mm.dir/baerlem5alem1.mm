include "cv.mm"
include "co.mm"
include "cfv.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "csn.mm"
include "eldifad.mm"
include "lmodsubdi.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmodsubvs.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "wceq.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lmodass.mm"
include "syl13anc.mm"
include "3eqtrd.mm"
include "cminusg.mm"
include "lmodvacl.mm"
include "eqid.mm"
include "grpsubval.mm"
include "lmodvsdi.mm"
include "lmodvsneg.mm"
include "clss.mm"
include "cpr.mm"
include "lspprcl.mm"
include "lsppreli.mm"
include "cabl.mm"
include "lmodabl.mm"
include "abl32.mm"
include "3eqtr3d.mm"
include "lvecindp.mm"
include "simprd.mm"
include "lvecindp2.mm"
include "simpld.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"

theorem baerlem5alem1
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let ve: setvar e
  let vj: setvar j
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
  assume baerlem5a.a1: |- ( ph -> a e. B )
  assume baerlem5a.b1: |- ( ph -> b e. B )
  assume baerlem5a.d1: |- ( ph -> d e. B )
  assume baerlem5a.e1: |- ( ph -> e e. B )
  assume baerlem5a.j1: |- ( ph -> j = ( ( a .x. ( X .- Y ) ) .+ ( b .x. Z ) ) )
  assume baerlem5a.j2: |- ( ph -> j = ( ( d .x. ( X .- Z ) ) .+ ( e .x. Y ) ) )


  assert |- ( ph -> j = ( a .x. ( X .- ( Y .+ Z ) ) ) )

  proof
    wph
    vj
    cv
    #
    va
    cv
    #
    cX
    c.x
    co
    #
    @1
    cI
    cfv
    #
    cY
    c.x
    co
    #
    vb
    cv
    #
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    c.pl
    co
    #
    @1
    cX
    cY
    cZ
    c.pl
    co
    #
    c.mi
    co
    c.x
    co
    #
    wph
    @0
    @1
    cX
    cY
    c.mi
    co
    c.x
    co
    #
    @6
    c.pl
    co
    @2
    @4
    c.pl
    co
    #
    @6
    c.pl
    co
    #
    @8
    baerlem5a.j1
    wph
    @11
    @12
    @6
    c.pl
    wph
    @11
    @2
    @1
    cY
    c.x
    co
    c.mi
    co
    @12
    wph
    @1
    c.x
    cR
    cB
    c.mi
    cV
    cW
    cX
    cY
    baerlem3.v
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.m
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    baerlem3.w
    cW
    lveclmod
    #
    syl
    #
    baerlem5a.a1
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
    lmodsubdi
    wph
    @1
    c.pl
    c.x
    cR
    cB
    c.mi
    cI
    cV
    cW
    @2
    cY
    baerlem3.v
    baerlem3.p
    baerlem3.m
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.i
    @17
    baerlem5a.a1
    wph
    @15
    @1
    cB
    wcel
    #
    cX
    cV
    wcel
    #
    @2
    cV
    wcel
    #
    @17
    baerlem5a.a1
    baerlem3.x
    @1
    c.x
    cR
    cB
    cV
    cW
    cX
    baerlem3.v
    baerlem3.r
    baerlem3.t
    baerlem3.b
    lmodvscl
    syl3anc
    #
    @19
    lmodsubvs
    eqtrd
    oveq1d
    wph
    @15
    @22
    @4
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    @13
    @8
    wceq
    @17
    @23
    wph
    @15
    @3
    cB
    wcel
    #
    cY
    cV
    wcel
    #
    @24
    @17
    wph
    cR
    cgrp
    wcel
    #
    @20
    @26
    wph
    @15
    cR
    crg
    wcel
    @28
    @17
    cR
    cW
    baerlem3.r
    lmodring
    cR
    ringgrp
    3syl
    #
    baerlem5a.a1
    cB
    cR
    cI
    @1
    baerlem3.b
    baerlem3.i
    grpinvcl
    syl2anc
    #
    @19
    @3
    c.x
    cR
    cB
    cV
    cW
    cY
    baerlem3.v
    baerlem3.r
    baerlem3.t
    baerlem3.b
    lmodvscl
    syl3anc
    wph
    @15
    @5
    cB
    wcel
    cZ
    cV
    wcel
    #
    @25
    @17
    baerlem5a.b1
    wph
    cZ
    cV
    @18
    baerlem3.z
    eldifad
    #
    @5
    c.x
    cR
    cB
    cV
    cW
    cZ
    baerlem3.v
    baerlem3.r
    baerlem3.t
    baerlem3.b
    lmodvscl
    syl3anc
    c.pl
    cV
    cW
    @2
    @4
    @6
    baerlem3.v
    baerlem3.p
    lmodass
    syl13anc
    3eqtrd
    #
    wph
    @2
    @1
    @9
    c.x
    co
    #
    c.mi
    co
    #
    @2
    @34
    cW
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    @10
    @8
    wph
    @22
    @34
    cV
    wcel
    #
    @35
    @38
    wceq
    @23
    wph
    @15
    @20
    @9
    cV
    wcel
    #
    @39
    @17
    baerlem5a.a1
    wph
    @15
    @27
    @31
    @40
    @17
    @19
    @32
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
    @1
    c.x
    cR
    cB
    cV
    cW
    @9
    baerlem3.v
    baerlem3.r
    baerlem3.t
    baerlem3.b
    lmodvscl
    syl3anc
    cV
    c.pl
    cW
    @36
    c.mi
    @2
    @34
    baerlem3.v
    baerlem3.p
    @36
    eqid
    #
    baerlem3.m
    grpsubval
    syl2anc
    wph
    @1
    c.x
    cR
    cB
    c.mi
    cV
    cW
    cX
    @9
    baerlem3.v
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.m
    @17
    baerlem5a.a1
    baerlem3.x
    @41
    lmodsubdi
    wph
    @7
    @37
    @2
    c.pl
    wph
    @3
    @9
    c.x
    co
    #
    @4
    @3
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    @37
    @7
    wph
    @15
    @26
    @27
    @31
    @43
    @45
    wceq
    @17
    @30
    @19
    @32
    c.pl
    @3
    c.x
    cR
    cB
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.t
    baerlem3.b
    lmodvsdi
    syl13anc
    wph
    cV
    @1
    c.x
    cR
    cB
    cI
    @36
    cW
    @9
    baerlem3.v
    baerlem3.r
    baerlem3.t
    @42
    baerlem3.b
    baerlem3.i
    @17
    @41
    baerlem5a.a1
    lmodvsneg
    wph
    @6
    @44
    @4
    c.pl
    wph
    @5
    @3
    cZ
    c.x
    wph
    @5
    vd
    cv
    #
    cI
    cfv
    #
    @3
    wph
    @3
    ve
    cv
    #
    wceq
    @5
    @47
    wceq
    wph
    @3
    @5
    @48
    @47
    c.pl
    c.x
    cR
    cB
    cN
    cV
    cW
    cY
    cZ
    c.0
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.b
    baerlem3.t
    baerlem3.o
    baerlem3.n
    baerlem3.w
    baerlem3.y
    baerlem3.z
    @30
    baerlem5a.b1
    baerlem5a.e1
    wph
    @28
    @46
    cB
    wcel
    #
    @47
    cB
    wcel
    #
    @29
    baerlem5a.d1
    cB
    cR
    cI
    @46
    baerlem3.b
    baerlem3.i
    grpinvcl
    syl2anc
    #
    baerlem3.d
    wph
    @1
    @46
    wceq
    #
    @7
    @48
    cY
    c.x
    co
    #
    @47
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    wph
    @1
    @46
    c.pl
    cW
    clss
    cfv
    #
    c.x
    cY
    cZ
    cpr
    cN
    cfv
    cR
    cB
    cV
    cW
    cX
    @7
    @55
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.b
    baerlem3.t
    @57
    eqid
    #
    baerlem3.w
    wph
    @57
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    @58
    baerlem3.n
    @17
    @19
    @32
    lspprcl
    baerlem3.x
    baerlem3.c
    wph
    @3
    @5
    c.pl
    c.x
    cR
    cB
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.p
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.n
    @17
    @30
    baerlem5a.b1
    @19
    @32
    lsppreli
    wph
    @48
    @47
    c.pl
    c.x
    cR
    cB
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    baerlem3.p
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.n
    @17
    baerlem5a.e1
    @51
    @19
    @32
    lsppreli
    baerlem5a.a1
    baerlem5a.d1
    wph
    @0
    @46
    cX
    cZ
    c.mi
    co
    c.x
    co
    #
    @53
    c.pl
    co
    #
    @8
    @46
    cX
    c.x
    co
    #
    @55
    c.pl
    co
    #
    baerlem5a.j2
    @33
    wph
    @60
    @61
    @54
    c.pl
    co
    #
    @53
    c.pl
    co
    @61
    @53
    c.pl
    co
    @54
    c.pl
    co
    #
    @62
    wph
    @59
    @63
    @53
    c.pl
    wph
    @59
    @61
    @46
    cZ
    c.x
    co
    c.mi
    co
    @63
    wph
    @46
    c.x
    cR
    cB
    c.mi
    cV
    cW
    cX
    cZ
    baerlem3.v
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.m
    @17
    baerlem5a.d1
    baerlem3.x
    @32
    lmodsubdi
    wph
    @46
    c.pl
    c.x
    cR
    cB
    c.mi
    cI
    cV
    cW
    @61
    cZ
    baerlem3.v
    baerlem3.p
    baerlem3.m
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.i
    @17
    baerlem5a.d1
    wph
    @15
    @49
    @21
    @61
    cV
    wcel
    #
    @17
    baerlem5a.d1
    baerlem3.x
    @46
    c.x
    cR
    cB
    cV
    cW
    cX
    baerlem3.v
    baerlem3.r
    baerlem3.t
    baerlem3.b
    lmodvscl
    syl3anc
    #
    @32
    lmodsubvs
    eqtrd
    oveq1d
    wph
    cV
    c.pl
    cW
    @61
    @54
    @53
    baerlem3.v
    baerlem3.p
    wph
    @14
    @15
    cW
    cabl
    wcel
    baerlem3.w
    @16
    cW
    lmodabl
    3syl
    @66
    wph
    @15
    @50
    @31
    @54
    cV
    wcel
    #
    @17
    @51
    @32
    @47
    c.x
    cR
    cB
    cV
    cW
    cZ
    baerlem3.v
    baerlem3.r
    baerlem3.t
    baerlem3.b
    lmodvscl
    syl3anc
    #
    wph
    @15
    @48
    cB
    wcel
    @27
    @53
    cV
    wcel
    #
    @17
    baerlem5a.e1
    @19
    @48
    c.x
    cR
    cB
    cV
    cW
    cY
    baerlem3.v
    baerlem3.r
    baerlem3.t
    baerlem3.b
    lmodvscl
    syl3anc
    #
    abl32
    wph
    @15
    @65
    @69
    @67
    @64
    @62
    wceq
    @17
    @66
    @70
    @68
    c.pl
    cV
    cW
    @61
    @53
    @54
    baerlem3.v
    baerlem3.p
    lmodass
    syl13anc
    3eqtrd
    3eqtr3d
    lvecindp
    #
    simprd
    lvecindp2
    simprd
    wph
    @1
    @46
    cI
    wph
    @52
    @56
    @71
    simpld
    fveq2d
    eqtr4d
    oveq1d
    oveq2d
    3eqtr4rd
    oveq2d
    3eqtr4rd
    eqtrd
end
