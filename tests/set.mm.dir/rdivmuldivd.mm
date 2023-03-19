include "co.mm"
include "cinvr.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "dvrval.mm"
include "oveq1d.mm"
include "syl2anc.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "unitss.mm"
include "unitinvcl.mm"
include "sseldi.mm"
include "dvrcl.mm"
include "syl3anc.mm"
include "ringass.mm"
include "syl13anc.mm"
include "crngcom.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cmgp.mm"
include "cress.mm"
include "cplusg.mm"
include "cgrp.mm"
include "unitgrp.mm"
include "unitgrpbas.mm"
include "invrfval.mm"
include "grpinvadd.mm"
include "cvv.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mgpress.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "cmulr.mm"
include "ressmulr.mm"
include "ax-mp.mm"
include "mgpplusg.mm"
include "syl6reqr.mm"
include "oveqd.mm"
include "3eqtr4d.mm"
include "ringcl.mm"
include "unitmulcl.mm"
include "eqtr4d.mm"
include "3eqtr3rd.mm"
include "3eqtr4rd.mm"
include "eqtrd.mm"

theorem rdivmuldivd
  let wph: wff ph
  let cB: class B
  let c.dv: class ./
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dvrdir.b: |- B = ( Base ` R )
  assume dvrdir.u: |- U = ( Unit ` R )
  assume dvrdir.p: |- .+ = ( +g ` R )
  assume dvrdir.t: |- ./ = ( /r ` R )
  assume rdivmuldivd.p: |- .x. = ( .r ` R )
  assume rdivmuldivd.r: |- ( ph -> R e. CRing )
  assume rdivmuldivd.a: |- ( ph -> X e. B )
  assume rdivmuldivd.b: |- ( ph -> Y e. U )
  assume rdivmuldivd.c: |- ( ph -> Z e. B )
  assume rdivmuldivd.d: |- ( ph -> W e. U )


  assert |- ( ph -> ( ( X ./ Y ) .x. ( Z ./ W ) ) = ( ( X .x. Z ) ./ ( Y .x. W ) ) )

  proof
    wph
    cX
    cY
    c.dv
    co
    #
    cZ
    cW
    c.dv
    co
    #
    c.x
    co
    #
    cX
    @1
    cY
    cR
    cinvr
    cfv
    #
    cfv
    #
    c.x
    co
    #
    c.x
    co
    #
    cX
    cZ
    c.x
    co
    #
    cY
    cW
    c.x
    co
    #
    c.dv
    co
    #
    wph
    @2
    cX
    @4
    c.x
    co
    #
    @1
    c.x
    co
    #
    cX
    @4
    @1
    c.x
    co
    #
    c.x
    co
    #
    @6
    wph
    cX
    cB
    wcel
    #
    cY
    cU
    wcel
    #
    @2
    @11
    wceq
    rdivmuldivd.a
    rdivmuldivd.b
    @14
    @15
    wa
    @0
    @10
    @1
    c.x
    cB
    c.dv
    cR
    c.x
    cU
    @3
    cX
    cY
    dvrdir.b
    rdivmuldivd.p
    dvrdir.u
    @3
    eqid
    #
    dvrdir.t
    dvrval
    oveq1d
    syl2anc
    wph
    cR
    crg
    wcel
    #
    @14
    @4
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @11
    @13
    wceq
    wph
    cR
    ccrg
    wcel
    #
    @17
    rdivmuldivd.r
    cR
    crngring
    syl
    #
    rdivmuldivd.a
    wph
    cU
    cB
    @4
    cB
    cR
    cU
    dvrdir.b
    dvrdir.u
    unitss
    #
    wph
    @17
    @15
    @4
    cU
    wcel
    @21
    rdivmuldivd.b
    cR
    cU
    @3
    cY
    dvrdir.u
    @16
    unitinvcl
    syl2anc
    sseldi
    #
    wph
    @17
    cZ
    cB
    wcel
    #
    cW
    cU
    wcel
    #
    @19
    @21
    rdivmuldivd.c
    rdivmuldivd.d
    cB
    c.dv
    cR
    cU
    cZ
    cW
    dvrdir.b
    dvrdir.u
    dvrdir.t
    dvrcl
    syl3anc
    #
    cB
    cR
    c.x
    cX
    @4
    @1
    dvrdir.b
    rdivmuldivd.p
    ringass
    syl13anc
    wph
    @12
    @5
    cX
    c.x
    wph
    @20
    @18
    @19
    @12
    @5
    wceq
    rdivmuldivd.r
    @23
    @26
    cB
    cR
    c.x
    @4
    @1
    dvrdir.b
    rdivmuldivd.p
    crngcom
    syl3anc
    oveq2d
    3eqtrd
    wph
    @7
    @8
    @3
    cfv
    #
    c.x
    co
    #
    @7
    cW
    @3
    cfv
    #
    @4
    c.x
    co
    #
    c.x
    co
    #
    @9
    @6
    wph
    @27
    @30
    @7
    c.x
    wph
    cY
    cW
    cR
    cmgp
    cfv
    #
    cU
    cress
    co
    #
    cplusg
    cfv
    #
    co
    #
    @3
    cfv
    #
    @29
    @4
    @34
    co
    #
    @27
    @30
    wph
    @33
    cgrp
    wcel
    #
    @15
    @25
    @36
    @37
    wceq
    wph
    @17
    @38
    @21
    cR
    cU
    @33
    dvrdir.u
    @33
    eqid
    #
    unitgrp
    syl
    rdivmuldivd.b
    rdivmuldivd.d
    cU
    @34
    @33
    @3
    cY
    cW
    cR
    cU
    @33
    dvrdir.u
    @39
    unitgrpbas
    @34
    eqid
    cR
    cU
    @33
    @3
    dvrdir.u
    @39
    @16
    invrfval
    grpinvadd
    syl3anc
    wph
    @8
    @35
    @3
    wph
    c.x
    @34
    cY
    cW
    wph
    @34
    cR
    cU
    cress
    co
    #
    cmgp
    cfv
    #
    cplusg
    cfv
    c.x
    wph
    @33
    @41
    cplusg
    wph
    @17
    cU
    cvv
    wcel
    #
    @33
    @41
    wceq
    @21
    cU
    cR
    cui
    cfv
    cvv
    dvrdir.u
    cR
    cui
    fvex
    eqeltri
    #
    cU
    cR
    @40
    @32
    crg
    cvv
    @40
    eqid
    #
    @32
    eqid
    mgpress
    sylancl
    fveq2d
    @40
    c.x
    @41
    @41
    eqid
    @42
    c.x
    @40
    cmulr
    cfv
    wceq
    @43
    cU
    cR
    @40
    c.x
    cvv
    @44
    rdivmuldivd.p
    ressmulr
    ax-mp
    mgpplusg
    syl6reqr
    #
    oveqd
    fveq2d
    wph
    c.x
    @34
    @29
    @4
    @45
    oveqd
    3eqtr4d
    oveq2d
    wph
    @7
    cB
    wcel
    #
    @8
    cU
    wcel
    #
    @9
    @28
    wceq
    wph
    @17
    @14
    @24
    @46
    @21
    rdivmuldivd.a
    rdivmuldivd.c
    cB
    cR
    c.x
    cX
    cZ
    dvrdir.b
    rdivmuldivd.p
    ringcl
    syl3anc
    #
    wph
    @17
    @15
    @25
    @47
    @21
    rdivmuldivd.b
    rdivmuldivd.d
    cR
    c.x
    cU
    cY
    cW
    dvrdir.u
    rdivmuldivd.p
    unitmulcl
    syl3anc
    cB
    c.dv
    cR
    c.x
    cU
    @3
    @7
    @8
    dvrdir.b
    rdivmuldivd.p
    dvrdir.u
    @16
    dvrdir.t
    dvrval
    syl2anc
    wph
    @7
    @29
    c.x
    co
    #
    @4
    c.x
    co
    #
    cX
    @1
    c.x
    co
    #
    @4
    c.x
    co
    #
    @31
    @6
    wph
    @49
    @51
    @4
    c.x
    wph
    @49
    cX
    cZ
    @29
    c.x
    co
    #
    c.x
    co
    #
    @51
    wph
    @17
    @14
    @24
    @29
    cB
    wcel
    #
    @49
    @54
    wceq
    @21
    rdivmuldivd.a
    rdivmuldivd.c
    wph
    cU
    cB
    @29
    @22
    wph
    @17
    @25
    @29
    cU
    wcel
    @21
    rdivmuldivd.d
    cR
    cU
    @3
    cW
    dvrdir.u
    @16
    unitinvcl
    syl2anc
    sseldi
    #
    cB
    cR
    c.x
    cX
    cZ
    @29
    dvrdir.b
    rdivmuldivd.p
    ringass
    syl13anc
    wph
    @1
    @53
    cX
    c.x
    wph
    @24
    @25
    @1
    @53
    wceq
    rdivmuldivd.c
    rdivmuldivd.d
    cB
    c.dv
    cR
    c.x
    cU
    @3
    cZ
    cW
    dvrdir.b
    rdivmuldivd.p
    dvrdir.u
    @16
    dvrdir.t
    dvrval
    syl2anc
    oveq2d
    eqtr4d
    oveq1d
    wph
    @17
    @46
    @55
    @18
    @50
    @31
    wceq
    @21
    @48
    @56
    @23
    cB
    cR
    c.x
    @7
    @29
    @4
    dvrdir.b
    rdivmuldivd.p
    ringass
    syl13anc
    wph
    @17
    @14
    @19
    @18
    @52
    @6
    wceq
    @21
    rdivmuldivd.a
    @26
    @23
    cB
    cR
    c.x
    cX
    @1
    @4
    dvrdir.b
    rdivmuldivd.p
    ringass
    syl13anc
    3eqtr3rd
    3eqtr4rd
    eqtrd
end
