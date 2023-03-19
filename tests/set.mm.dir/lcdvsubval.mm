include "co.mm"
include "cfv.mm"
include "csca.mm"
include "cur.mm"
include "cminusg.mm"
include "cvsca.mm"
include "cplusg.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "lmodvsubval2.mm"
include "syl3anc.mm"
include "fveq1d.mm"
include "cbs.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "syl.mm"
include "crg.mm"
include "lmodring.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lcdsbase.mm"
include "eleqtrd.mm"
include "lcdvscl.mm"
include "lcdvaddval.mm"
include "cmulr.mm"
include "lcdneg.mm"
include "lcd1.mm"
include "fveq12d.mm"
include "oveq1d.mm"
include "dvhlmod.mm"
include "ringgrp.mm"
include "lmod1cl.mm"
include "lcdvsval.mm"
include "lcdvbasecl.mm"
include "rngnegr.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "grpsubval.mm"
include "eqtr4d.mm"

theorem lcdvsubval
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let cX: class X
  assume lcdvsubval.h: |- H = ( LHyp ` K )
  assume lcdvsubval.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvsubval.v: |- V = ( Base ` U )
  assume lcdvsubval.r: |- R = ( Scalar ` U )
  assume lcdvsubval.s: |- S = ( -g ` R )
  assume lcdvsubval.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvsubval.d: |- D = ( Base ` C )
  assume lcdvsubval.m: |- .- = ( -g ` C )
  assume lcdvsubval.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvsubval.f: |- ( ph -> F e. D )
  assume lcdvsubval.g: |- ( ph -> G e. D )
  assume lcdvsubval.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( F .- G ) ` X ) = ( ( F ` X ) S ( G ` X ) ) )

  proof
    wph
    cX
    cF
    cG
    c.mi
    co
    #
    cfv
    cX
    cF
    cC
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
    cG
    cC
    cvsca
    cfv
    #
    co
    #
    cC
    cplusg
    cfv
    #
    co
    #
    cfv
    cX
    cF
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
    cG
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
    cC
    clmod
    wcel
    #
    cF
    cD
    wcel
    cG
    cD
    wcel
    @0
    @8
    wceq
    wph
    cC
    cH
    cK
    cW
    lcdvsubval.h
    lcdvsubval.c
    lcdvsubval.k
    lcdlmod
    #
    lcdvsubval.f
    lcdvsubval.g
    cF
    cG
    @7
    @5
    @2
    @1
    c.mi
    @3
    cD
    cC
    lcdvsubval.d
    @7
    eqid
    #
    lcdvsubval.m
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
    cC
    cD
    @11
    @7
    cR
    cU
    cF
    @6
    cH
    cK
    cV
    cW
    cX
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.v
    lcdvsubval.r
    @11
    eqid
    #
    lcdvsubval.c
    lcdvsubval.d
    @17
    lcdvsubval.k
    lcdvsubval.f
    wph
    cC
    cR
    cbs
    cfv
    #
    cR
    @5
    cU
    cG
    cH
    cK
    cD
    cW
    @4
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.r
    @23
    eqid
    #
    lcdvsubval.c
    lcdvsubval.d
    @19
    lcdvsubval.k
    wph
    @4
    @1
    cbs
    cfv
    #
    @23
    wph
    @1
    cgrp
    wcel
    #
    @2
    @25
    wcel
    #
    @4
    @25
    wcel
    wph
    @15
    @26
    @16
    @1
    cC
    @18
    lmodfgrp
    syl
    wph
    @1
    crg
    wcel
    #
    @27
    wph
    @15
    @28
    @16
    @1
    cC
    @18
    lmodring
    syl
    @25
    @1
    @2
    @25
    eqid
    #
    @21
    ringidcl
    syl
    @25
    @1
    @3
    @2
    @29
    @20
    grpinvcl
    syl2anc
    wph
    cC
    @25
    @1
    cU
    cR
    cH
    cK
    @23
    cW
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.r
    @24
    lcdvsubval.c
    @18
    @29
    lcdvsubval.k
    lcdsbase
    eleqtrd
    lcdvsubval.g
    lcdvscl
    lcdvsubval.x
    lcdvaddval
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
    @31
    @9
    @11
    wph
    @10
    cX
    cR
    cur
    cfv
    #
    @30
    cfv
    #
    cG
    @5
    co
    #
    cfv
    @13
    @34
    cR
    cmulr
    cfv
    #
    co
    @31
    wph
    cX
    @6
    @35
    wph
    @4
    @34
    cG
    @5
    wph
    @2
    @33
    @3
    @30
    wph
    cC
    cR
    @1
    cU
    cH
    cK
    @30
    @3
    cW
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.r
    @30
    eqid
    #
    lcdvsubval.c
    @18
    @20
    lcdvsubval.k
    lcdneg
    wph
    cC
    @1
    cU
    @33
    cR
    cH
    @2
    cK
    cW
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.r
    @33
    eqid
    #
    lcdvsubval.c
    @18
    @21
    lcdvsubval.k
    lcd1
    fveq12d
    oveq1d
    fveq1d
    wph
    cX
    cC
    @23
    cR
    @5
    @36
    cU
    cD
    cG
    cH
    cK
    cV
    cW
    @34
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.v
    lcdvsubval.r
    @24
    @36
    eqid
    #
    lcdvsubval.c
    lcdvsubval.d
    @19
    lcdvsubval.k
    wph
    cR
    cgrp
    wcel
    #
    @33
    @23
    wcel
    #
    @34
    @23
    wcel
    wph
    cR
    crg
    wcel
    #
    @40
    wph
    cU
    clmod
    wcel
    #
    @42
    wph
    cU
    cH
    cK
    cW
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.k
    dvhlmod
    #
    cR
    cU
    lcdvsubval.r
    lmodring
    syl
    #
    cR
    ringgrp
    syl
    wph
    @43
    @41
    @44
    @33
    cR
    @23
    cU
    lcdvsubval.r
    @24
    @38
    lmod1cl
    syl
    @23
    cR
    @30
    @33
    @24
    @37
    grpinvcl
    syl2anc
    lcdvsubval.g
    lcdvsubval.x
    lcdvsval
    wph
    @23
    cR
    @36
    @33
    @30
    @13
    @24
    @39
    @38
    @37
    @45
    wph
    cC
    @23
    cR
    cU
    cD
    cG
    cH
    cK
    cV
    cW
    cX
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.v
    lcdvsubval.r
    @24
    lcdvsubval.c
    lcdvsubval.d
    lcdvsubval.k
    lcdvsubval.g
    lcdvsubval.x
    lcdvbasecl
    #
    rngnegr
    3eqtrd
    oveq2d
    wph
    @9
    @23
    wcel
    @13
    @23
    wcel
    @14
    @32
    wceq
    wph
    cC
    @23
    cR
    cU
    cD
    cF
    cH
    cK
    cV
    cW
    cX
    lcdvsubval.h
    lcdvsubval.u
    lcdvsubval.v
    lcdvsubval.r
    @24
    lcdvsubval.c
    lcdvsubval.d
    lcdvsubval.k
    lcdvsubval.f
    lcdvsubval.x
    lcdvbasecl
    @46
    @23
    @11
    cR
    @30
    cS
    @9
    @13
    @24
    @22
    @37
    lcdvsubval.s
    grpsubval
    syl2anc
    eqtr4d
    3eqtrd
end
