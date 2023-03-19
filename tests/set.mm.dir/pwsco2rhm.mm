include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "rhmrcl1.mm"
include "syl.mm"
include "pwsring.mm"
include "syl2anc.mm"
include "rhmrcl2.mm"
include "jca.mm"
include "rhmghm.mm"
include "ghmmhm.mm"
include "pwsco2mhm.mm"
include "cgrp.mm"
include "wceq.mm"
include "ringgrp.mm"
include "ghmmhmb.mm"
include "eleqtrrd.mm"
include "cpws.mm"
include "cbs.mm"
include "eqid.mm"
include "rhmmhm.mm"
include "cmap.mm"
include "pwsbas.mm"
include "syl6eqr.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "eqtr3d.mm"
include "mpteq1d.mm"
include "eqidd.mm"
include "cplusg.mm"
include "pwsmgp.mm"
include "simpld.mm"
include "simprd.mm"
include "oveqdr.mm"
include "mhmpropd.mm"
include "3eltr4d.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem pwsco2rhm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume pwsco2rhm.y: |- Y = ( R ^s A )
  assume pwsco2rhm.z: |- Z = ( S ^s A )
  assume pwsco2rhm.b: |- B = ( Base ` Y )
  assume pwsco2rhm.a: |- ( ph -> A e. V )
  assume pwsco2rhm.f: |- ( ph -> F e. ( R RingHom S ) )

  disjoint A g
  disjoint g ph
  disjoint R g
  disjoint S g
  disjoint Y g
  disjoint B g
  disjoint F g
  disjoint Z g
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> ( g e. B |-> ( F o. g ) ) e. ( Y RingHom Z ) )

  proof
    wph
    cY
    crg
    wcel
    #
    cZ
    crg
    wcel
    #
    wa
    vg
    cB
    cF
    vg
    cv
    ccom
    #
    cmpt
    #
    cY
    cZ
    cghm
    co
    #
    wcel
    #
    @3
    cY
    cmgp
    cfv
    #
    cZ
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    wa
    @3
    cY
    cZ
    crh
    co
    wcel
    wph
    @0
    @1
    wph
    cR
    crg
    wcel
    #
    cA
    cV
    wcel
    #
    @0
    wph
    cF
    cR
    cS
    crh
    co
    wcel
    #
    @10
    pwsco2rhm.f
    cR
    cS
    cF
    rhmrcl1
    syl
    #
    pwsco2rhm.a
    cR
    cA
    cV
    cY
    pwsco2rhm.y
    pwsring
    syl2anc
    #
    wph
    cS
    crg
    wcel
    #
    @11
    @1
    wph
    @12
    @15
    pwsco2rhm.f
    cR
    cS
    cF
    rhmrcl2
    syl
    #
    pwsco2rhm.a
    cS
    cA
    cV
    cZ
    pwsco2rhm.z
    pwsring
    syl2anc
    #
    jca
    wph
    @5
    @9
    wph
    @3
    cY
    cZ
    cmhm
    co
    #
    @4
    wph
    cA
    cB
    cR
    cS
    vg
    cF
    cV
    cY
    cZ
    pwsco2rhm.y
    pwsco2rhm.z
    pwsco2rhm.b
    pwsco2rhm.a
    wph
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    cF
    cR
    cS
    cmhm
    co
    wcel
    wph
    @12
    @19
    pwsco2rhm.f
    cR
    cS
    cF
    rhmghm
    syl
    cR
    cS
    cF
    ghmmhm
    syl
    pwsco2mhm
    wph
    cY
    cgrp
    wcel
    #
    cZ
    cgrp
    wcel
    #
    @4
    @18
    wceq
    wph
    @0
    @20
    @14
    cY
    ringgrp
    syl
    wph
    @1
    @21
    @17
    cZ
    ringgrp
    syl
    cY
    cZ
    ghmmhmb
    syl2anc
    eleqtrrd
    wph
    vg
    cR
    cmgp
    cfv
    #
    cA
    cpws
    co
    #
    cbs
    cfv
    #
    @2
    cmpt
    @23
    cS
    cmgp
    cfv
    #
    cA
    cpws
    co
    #
    cmhm
    co
    @3
    @8
    wph
    cA
    @24
    @22
    @25
    vg
    cF
    cV
    @23
    @26
    @23
    eqid
    #
    @26
    eqid
    #
    @24
    eqid
    #
    pwsco2rhm.a
    wph
    @12
    cF
    @22
    @25
    cmhm
    co
    wcel
    pwsco2rhm.f
    cR
    cS
    cF
    @22
    @25
    @22
    eqid
    #
    @25
    eqid
    #
    rhmmhm
    syl
    pwsco2mhm
    wph
    vg
    cB
    @24
    @2
    wph
    cR
    cbs
    cfv
    #
    cA
    cmap
    co
    #
    cB
    @24
    wph
    @33
    cY
    cbs
    cfv
    #
    cB
    wph
    @10
    @11
    @33
    @34
    wceq
    @13
    pwsco2rhm.a
    @32
    cR
    cA
    crg
    cV
    cY
    pwsco2rhm.y
    @32
    eqid
    #
    pwsbas
    syl2anc
    pwsco2rhm.b
    syl6eqr
    wph
    @22
    cmnd
    wcel
    #
    @11
    @33
    @24
    wceq
    wph
    @10
    @36
    @13
    cR
    @22
    @30
    ringmgp
    syl
    pwsco2rhm.a
    @32
    @22
    cA
    cmnd
    cV
    @23
    @27
    @32
    cR
    @22
    @30
    @35
    mgpbas
    pwsbas
    syl2anc
    eqtr3d
    mpteq1d
    wph
    vx
    vy
    @6
    cbs
    cfv
    #
    @7
    cbs
    cfv
    #
    @6
    @7
    @23
    @26
    wph
    @37
    eqidd
    wph
    @38
    eqidd
    wph
    @37
    @24
    wceq
    #
    @6
    cplusg
    cfv
    #
    @23
    cplusg
    cfv
    #
    wceq
    #
    wph
    @10
    @11
    @39
    @42
    wa
    @13
    pwsco2rhm.a
    @37
    @24
    @40
    @41
    cR
    cA
    @22
    @6
    crg
    cV
    cY
    @23
    pwsco2rhm.y
    @30
    @27
    @6
    eqid
    #
    @37
    eqid
    @29
    @40
    eqid
    @41
    eqid
    pwsmgp
    syl2anc
    #
    simpld
    wph
    @38
    @26
    cbs
    cfv
    #
    wceq
    #
    @7
    cplusg
    cfv
    #
    @26
    cplusg
    cfv
    #
    wceq
    #
    wph
    @15
    @11
    @46
    @49
    wa
    @16
    pwsco2rhm.a
    @38
    @45
    @47
    @48
    cS
    cA
    @25
    @7
    crg
    cV
    cZ
    @26
    pwsco2rhm.z
    @31
    @28
    @7
    eqid
    #
    @38
    eqid
    @45
    eqid
    @47
    eqid
    @48
    eqid
    pwsmgp
    syl2anc
    #
    simpld
    wph
    vx
    cv
    #
    @37
    wcel
    vy
    cv
    #
    @37
    wcel
    wa
    vx
    vy
    @40
    @41
    wph
    @39
    @42
    @44
    simprd
    oveqdr
    wph
    @52
    @38
    wcel
    @53
    @38
    wcel
    wa
    vx
    vy
    @47
    @48
    wph
    @46
    @49
    @51
    simprd
    oveqdr
    mhmpropd
    3eltr4d
    jca
    cY
    cZ
    @3
    @6
    @7
    @43
    @50
    isrhm
    sylanbrc
end
