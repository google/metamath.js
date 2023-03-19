include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "clss.mm"
include "cpr.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "csn.mm"
include "eldifad.mm"
include "lspprcl.mm"
include "lsppreli.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "ringgrp.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lmod0cl.mm"
include "lmodacl.mm"
include "syl3anc.mm"
include "lmodvscl.mm"
include "lmodvacl.mm"
include "lmod0vlid.mm"
include "lmod0vs.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "lmodsubdi.mm"
include "lmodsubvs.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "lmodvsdir.mm"
include "cabl.mm"
include "lmodabl.mm"
include "abl32.mm"
include "eqtrd.mm"
include "lvecindp.mm"
include "simpld.mm"
include "eqtr3d.mm"

theorem baerlem5blem1
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
  assume baerlem5b.a1: |- ( ph -> a e. B )
  assume baerlem5b.b1: |- ( ph -> b e. B )
  assume baerlem5b.d1: |- ( ph -> d e. B )
  assume baerlem5b.e1: |- ( ph -> e e. B )
  assume baerlem5b.j1: |- ( ph -> j = ( ( a .x. Y ) .+ ( b .x. Z ) ) )
  assume baerlem5b.j2: |- ( ph -> j = ( ( d .x. ( X .- ( Y .+ Z ) ) ) .+ ( e .x. X ) ) )


  assert |- ( ph -> j = ( ( I ` d ) .x. ( Y .+ Z ) ) )

  proof
    wph
    vd
    cv
    #
    ve
    cv
    #
    c.pd
    co
    #
    cX
    c.x
    co
    #
    @0
    cI
    cfv
    #
    cY
    c.x
    co
    #
    @4
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
    @7
    vj
    cv
    #
    @4
    cY
    cZ
    c.pl
    co
    #
    c.x
    co
    #
    wph
    @8
    c.0
    @7
    c.pl
    co
    #
    @7
    wph
    @3
    c.0
    @7
    c.pl
    wph
    cQ
    cX
    c.x
    co
    #
    @3
    c.0
    wph
    cQ
    @2
    cX
    c.x
    wph
    cQ
    @2
    wceq
    va
    cv
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
    @7
    wceq
    wph
    cQ
    @2
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
    @18
    @7
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.b
    baerlem3.t
    @19
    eqid
    #
    baerlem3.w
    wph
    @19
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    @20
    baerlem3.n
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    #
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
    @23
    baerlem3.z
    eldifad
    #
    lspprcl
    baerlem3.x
    baerlem3.c
    wph
    @14
    @16
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
    @22
    baerlem5b.a1
    baerlem5b.b1
    @24
    @25
    lsppreli
    wph
    @4
    @4
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
    @22
    wph
    cR
    cgrp
    wcel
    #
    @0
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wph
    cR
    crg
    wcel
    #
    @26
    wph
    @21
    @29
    @22
    cR
    cW
    baerlem3.r
    lmodring
    syl
    cR
    ringgrp
    syl
    baerlem5b.d1
    cB
    cR
    cI
    @0
    baerlem3.b
    baerlem3.i
    grpinvcl
    syl2anc
    #
    @30
    @24
    @25
    lsppreli
    wph
    @21
    cQ
    cB
    wcel
    @22
    cR
    cB
    cW
    cQ
    baerlem3.r
    baerlem3.b
    baerlem3.q
    lmod0cl
    syl
    wph
    @21
    @27
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    @22
    baerlem5b.d1
    baerlem5b.e1
    c.pd
    cR
    cB
    cW
    @0
    @1
    baerlem3.r
    baerlem3.b
    baerlem3.a
    lmodacl
    syl3anc
    wph
    @13
    @18
    c.pl
    co
    #
    @9
    @8
    wph
    c.0
    @18
    c.pl
    co
    #
    @18
    @32
    @9
    wph
    @21
    @18
    cV
    wcel
    #
    @33
    @18
    wceq
    @22
    wph
    @21
    @15
    cV
    wcel
    #
    @17
    cV
    wcel
    #
    @34
    @22
    wph
    @21
    @14
    cB
    wcel
    cY
    cV
    wcel
    #
    @35
    @22
    baerlem5b.a1
    @24
    @14
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
    @21
    @16
    cB
    wcel
    cZ
    cV
    wcel
    #
    @36
    @22
    baerlem5b.b1
    @25
    @16
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
    @15
    @17
    baerlem3.v
    baerlem3.p
    lmodvacl
    syl3anc
    c.pl
    cV
    cW
    @18
    c.0
    baerlem3.v
    baerlem3.p
    baerlem3.o
    lmod0vlid
    syl2anc
    wph
    @13
    c.0
    @18
    c.pl
    wph
    @21
    cX
    cV
    wcel
    #
    @13
    c.0
    wceq
    @22
    baerlem3.x
    c.x
    cR
    cQ
    cV
    cW
    cX
    c.0
    baerlem3.v
    baerlem3.r
    baerlem3.t
    baerlem3.q
    baerlem3.o
    lmod0vs
    syl2anc
    #
    oveq1d
    baerlem5b.j1
    3eqtr4d
    wph
    @0
    cX
    @10
    c.mi
    co
    c.x
    co
    #
    @1
    cX
    c.x
    co
    #
    c.pl
    co
    @0
    cX
    c.x
    co
    #
    @7
    c.pl
    co
    #
    @42
    c.pl
    co
    #
    @9
    @8
    wph
    @41
    @44
    @42
    c.pl
    wph
    @41
    @43
    @0
    @10
    c.x
    co
    c.mi
    co
    @43
    @11
    c.pl
    co
    @44
    wph
    @0
    c.x
    cR
    cB
    c.mi
    cV
    cW
    cX
    @10
    baerlem3.v
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.m
    @22
    baerlem5b.d1
    baerlem3.x
    wph
    @21
    @37
    @38
    @10
    cV
    wcel
    @22
    @24
    @25
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
    lmodsubdi
    wph
    @0
    c.pl
    c.x
    cR
    cB
    c.mi
    cI
    cV
    cW
    @43
    @10
    baerlem3.v
    baerlem3.p
    baerlem3.m
    baerlem3.t
    baerlem3.r
    baerlem3.b
    baerlem3.i
    @22
    baerlem5b.d1
    wph
    @21
    @27
    @39
    @43
    cV
    wcel
    @22
    baerlem5b.d1
    baerlem3.x
    @0
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
    @46
    lmodsubvs
    wph
    @11
    @7
    @43
    c.pl
    wph
    @21
    @28
    @37
    @38
    @11
    @7
    wceq
    @22
    @30
    @24
    @25
    c.pl
    @4
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
    #
    oveq2d
    3eqtrd
    oveq1d
    baerlem5b.j2
    wph
    @8
    @43
    @42
    c.pl
    co
    #
    @7
    c.pl
    co
    @45
    wph
    @3
    @49
    @7
    c.pl
    wph
    @21
    @27
    @31
    @39
    @3
    @49
    wceq
    @22
    baerlem5b.d1
    baerlem5b.e1
    baerlem3.x
    c.pl
    c.pd
    @0
    @1
    c.x
    cR
    cB
    cV
    cW
    cX
    baerlem3.v
    baerlem3.p
    baerlem3.r
    baerlem3.t
    baerlem3.b
    baerlem3.a
    lmodvsdir
    syl13anc
    oveq1d
    wph
    cV
    c.pl
    cW
    @43
    @42
    @7
    baerlem3.v
    baerlem3.p
    wph
    @21
    cW
    cabl
    wcel
    @22
    cW
    lmodabl
    syl
    @47
    wph
    @21
    @31
    @39
    @42
    cV
    wcel
    @22
    baerlem5b.e1
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
    wph
    @21
    @5
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    @7
    cV
    wcel
    #
    @22
    wph
    @21
    @28
    @37
    @50
    @22
    @30
    @24
    @4
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
    @21
    @28
    @38
    @51
    @22
    @30
    @25
    @4
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
    @5
    @6
    baerlem3.v
    baerlem3.p
    lmodvacl
    syl3anc
    #
    abl32
    eqtrd
    3eqtr4d
    #
    eqtrd
    lvecindp
    simpld
    oveq1d
    @40
    eqtr3d
    oveq1d
    wph
    @21
    @52
    @12
    @7
    wceq
    @22
    @53
    c.pl
    cV
    cW
    @7
    c.0
    baerlem3.v
    baerlem3.p
    baerlem3.o
    lmod0vlid
    syl2anc
    eqtrd
    @54
    @48
    3eqtr4d
end
