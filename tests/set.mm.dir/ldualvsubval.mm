include "co.mm"
include "cfv.mm"
include "csca.mm"
include "cur.mm"
include "cminusg.mm"
include "cvsca.mm"
include "cplusg.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "lduallmod.mm"
include "eqid.mm"
include "ldualelvbase.mm"
include "lmodvsubval2.mm"
include "syl3anc.mm"
include "fveq1d.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "syl.mm"
include "crg.mm"
include "lmodring.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ldualsbase.mm"
include "eleqtrd.mm"
include "ldualvscl.mm"
include "ldualvaddval.mm"
include "cmulr.mm"
include "ldualneg.mm"
include "ldual1.mm"
include "fveq12d.mm"
include "oveq1d.mm"
include "ringgrp.mm"
include "lmod1cl.mm"
include "ldualvsval.mm"
include "lflcl.mm"
include "rngnegr.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "grpsubval.mm"
include "eqtr4d.mm"

theorem ldualvsubval
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let cX: class X
  assume ldualvsubval.v: |- V = ( Base ` W )
  assume ldualvsubval.r: |- R = ( Scalar ` W )
  assume ldualvsubval.s: |- S = ( -g ` R )
  assume ldualvsubval.f: |- F = ( LFnl ` W )
  assume ldualvsubval.d: |- D = ( LDual ` W )
  assume ldualvsubval.m: |- .- = ( -g ` D )
  assume ldualvsubval.w: |- ( ph -> W e. LMod )
  assume ldualvsubval.g: |- ( ph -> G e. F )
  assume ldualvsubval.h: |- ( ph -> H e. F )
  assume ldualvsubval.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( G .- H ) ` X ) = ( ( G ` X ) S ( H ` X ) ) )

  proof
    wph
    cX
    cG
    cH
    c.mi
    co
    #
    cfv
    cX
    cG
    cD
    csca
    cfv
    #
    cur
    cfv
    #
    @1
    cminusg
    cfv
    #
    cfv
    #
    cH
    cD
    cvsca
    cfv
    #
    co
    #
    cD
    cplusg
    cfv
    #
    co
    #
    cfv
    cX
    cG
    cfv
    #
    cX
    @6
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @9
    cX
    cH
    cfv
    #
    cS
    co
    #
    wph
    cX
    @0
    @8
    wph
    cD
    clmod
    wcel
    #
    cG
    cD
    cbs
    cfv
    #
    wcel
    cH
    @16
    wcel
    @0
    @8
    wceq
    wph
    cD
    cW
    ldualvsubval.d
    ldualvsubval.w
    lduallmod
    #
    wph
    cD
    cF
    cG
    @16
    cW
    clmod
    ldualvsubval.f
    ldualvsubval.d
    @16
    eqid
    #
    ldualvsubval.w
    ldualvsubval.g
    ldualelvbase
    wph
    cD
    cF
    cH
    @16
    cW
    clmod
    ldualvsubval.f
    ldualvsubval.d
    @18
    ldualvsubval.w
    ldualvsubval.h
    ldualelvbase
    cG
    cH
    @7
    @5
    @2
    @1
    c.mi
    @3
    @16
    cD
    @18
    @7
    eqid
    #
    ldualvsubval.m
    @1
    eqid
    #
    @5
    eqid
    #
    @3
    eqid
    #
    @2
    eqid
    #
    lmodvsubval2
    syl3anc
    fveq1d
    wph
    cD
    @11
    @7
    cR
    cF
    cG
    @6
    cV
    cW
    cX
    ldualvsubval.v
    ldualvsubval.r
    @11
    eqid
    #
    ldualvsubval.f
    ldualvsubval.d
    @19
    ldualvsubval.w
    ldualvsubval.g
    wph
    cD
    cR
    @5
    cF
    cH
    cR
    cbs
    cfv
    #
    cW
    @4
    ldualvsubval.f
    ldualvsubval.r
    @25
    eqid
    #
    ldualvsubval.d
    @21
    ldualvsubval.w
    wph
    @4
    @1
    cbs
    cfv
    #
    @25
    wph
    @1
    cgrp
    wcel
    #
    @2
    @27
    wcel
    #
    @4
    @27
    wcel
    wph
    @15
    @28
    @17
    @1
    cD
    @20
    lmodfgrp
    syl
    wph
    @1
    crg
    wcel
    #
    @29
    wph
    @15
    @30
    @17
    @1
    cD
    @20
    lmodring
    syl
    @27
    @1
    @2
    @27
    eqid
    #
    @23
    ringidcl
    syl
    @27
    @1
    @3
    @2
    @31
    @22
    grpinvcl
    syl2anc
    wph
    cD
    @1
    cR
    @27
    @25
    clmod
    cW
    ldualvsubval.r
    @26
    ldualvsubval.d
    @20
    @31
    ldualvsubval.w
    ldualsbase
    eleqtrd
    ldualvsubval.h
    ldualvscl
    ldualvsubval.x
    ldualvaddval
    wph
    @12
    @9
    @13
    cR
    cminusg
    cfv
    #
    cfv
    #
    @11
    co
    #
    @14
    wph
    @10
    @33
    @9
    @11
    wph
    @10
    cX
    cR
    cur
    cfv
    #
    @32
    cfv
    #
    cH
    @5
    co
    #
    cfv
    @13
    @36
    cR
    cmulr
    cfv
    #
    co
    @33
    wph
    cX
    @6
    @37
    wph
    @4
    @36
    cH
    @5
    wph
    @2
    @35
    @3
    @32
    wph
    cD
    cR
    @1
    @32
    @3
    cW
    ldualvsubval.r
    @32
    eqid
    #
    ldualvsubval.d
    @20
    @22
    ldualvsubval.w
    ldualneg
    wph
    cD
    cR
    @1
    @35
    @2
    cW
    ldualvsubval.r
    @35
    eqid
    #
    ldualvsubval.d
    @20
    @23
    ldualvsubval.w
    ldual1
    fveq12d
    oveq1d
    fveq1d
    wph
    cX
    cD
    cR
    @5
    @38
    cF
    cH
    @25
    cV
    cW
    @36
    clmod
    ldualvsubval.f
    ldualvsubval.v
    ldualvsubval.r
    @26
    @38
    eqid
    #
    ldualvsubval.d
    @21
    ldualvsubval.w
    wph
    cR
    cgrp
    wcel
    #
    @35
    @25
    wcel
    #
    @36
    @25
    wcel
    wph
    cR
    crg
    wcel
    #
    @42
    wph
    cW
    clmod
    wcel
    #
    @44
    ldualvsubval.w
    cR
    cW
    ldualvsubval.r
    lmodring
    syl
    #
    cR
    ringgrp
    syl
    wph
    @45
    @43
    ldualvsubval.w
    @35
    cR
    @25
    cW
    ldualvsubval.r
    @26
    @40
    lmod1cl
    syl
    @25
    cR
    @32
    @35
    @26
    @39
    grpinvcl
    syl2anc
    ldualvsubval.h
    ldualvsubval.x
    ldualvsval
    wph
    @25
    cR
    @38
    @35
    @32
    @13
    @26
    @41
    @40
    @39
    @46
    wph
    @45
    cH
    cF
    wcel
    cX
    cV
    wcel
    #
    @13
    @25
    wcel
    #
    ldualvsubval.w
    ldualvsubval.h
    ldualvsubval.x
    cR
    cF
    cH
    @25
    cV
    cW
    cX
    clmod
    ldualvsubval.r
    @26
    ldualvsubval.v
    ldualvsubval.f
    lflcl
    syl3anc
    #
    rngnegr
    3eqtrd
    oveq2d
    wph
    @9
    @25
    wcel
    #
    @48
    @14
    @34
    wceq
    wph
    @45
    cG
    cF
    wcel
    @47
    @50
    ldualvsubval.w
    ldualvsubval.g
    ldualvsubval.x
    cR
    cF
    cG
    @25
    cV
    cW
    cX
    clmod
    ldualvsubval.r
    @26
    ldualvsubval.v
    ldualvsubval.f
    lflcl
    syl3anc
    @49
    @25
    @11
    cR
    @32
    cS
    @9
    @13
    @26
    @24
    @39
    ldualvsubval.s
    grpsubval
    syl2anc
    eqtr4d
    3eqtrd
end
