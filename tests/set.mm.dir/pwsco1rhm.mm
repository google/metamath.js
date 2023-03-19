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
include "pwsring.mm"
include "syl2anc.mm"
include "jca.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "syl.mm"
include "pwsco1mhm.mm"
include "cgrp.mm"
include "wceq.mm"
include "ringgrp.mm"
include "ghmmhmb.mm"
include "eleqtrrd.mm"
include "cpws.mm"
include "cbs.mm"
include "eqid.mm"
include "ringmgp.mm"
include "cmap.mm"
include "pwsbas.mm"
include "syl6eqr.mm"
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

theorem pwsco1rhm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vg: setvar g
  let cF: class F
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume pwsco1rhm.y: |- Y = ( R ^s A )
  assume pwsco1rhm.z: |- Z = ( R ^s B )
  assume pwsco1rhm.c: |- C = ( Base ` Z )
  assume pwsco1rhm.r: |- ( ph -> R e. Ring )
  assume pwsco1rhm.a: |- ( ph -> A e. V )
  assume pwsco1rhm.b: |- ( ph -> B e. W )
  assume pwsco1rhm.f: |- ( ph -> F : A --> B )

  disjoint A g
  disjoint B g
  disjoint g ph
  disjoint R g
  disjoint Y g
  disjoint C g
  disjoint F g
  disjoint Z g
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> ( g e. C |-> ( g o. F ) ) e. ( Z RingHom Y ) )

  proof
    wph
    cZ
    crg
    wcel
    #
    cY
    crg
    wcel
    #
    wa
    vg
    cC
    vg
    cv
    cF
    ccom
    #
    cmpt
    #
    cZ
    cY
    cghm
    co
    #
    wcel
    #
    @3
    cZ
    cmgp
    cfv
    #
    cY
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
    cZ
    cY
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
    cB
    cW
    wcel
    #
    @0
    pwsco1rhm.r
    pwsco1rhm.b
    cR
    cB
    cW
    cZ
    pwsco1rhm.z
    pwsring
    syl2anc
    #
    wph
    @10
    cA
    cV
    wcel
    #
    @1
    pwsco1rhm.r
    pwsco1rhm.a
    cR
    cA
    cV
    cY
    pwsco1rhm.y
    pwsring
    syl2anc
    #
    jca
    wph
    @5
    @9
    wph
    @3
    cZ
    cY
    cmhm
    co
    #
    @4
    wph
    cA
    cB
    cC
    cR
    vg
    cF
    cV
    cW
    cY
    cZ
    pwsco1rhm.y
    pwsco1rhm.z
    pwsco1rhm.c
    wph
    @10
    cR
    cmnd
    wcel
    #
    pwsco1rhm.r
    cR
    ringmnd
    syl
    #
    pwsco1rhm.a
    pwsco1rhm.b
    pwsco1rhm.f
    pwsco1mhm
    wph
    cZ
    cgrp
    wcel
    #
    cY
    cgrp
    wcel
    #
    @4
    @15
    wceq
    wph
    @0
    @18
    @12
    cZ
    ringgrp
    syl
    wph
    @1
    @19
    @14
    cY
    ringgrp
    syl
    cZ
    cY
    ghmmhmb
    syl2anc
    eleqtrrd
    wph
    vg
    cR
    cmgp
    cfv
    #
    cB
    cpws
    co
    #
    cbs
    cfv
    #
    @2
    cmpt
    @21
    @20
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
    cB
    @22
    @20
    vg
    cF
    cV
    cW
    @23
    @21
    @23
    eqid
    #
    @21
    eqid
    #
    @22
    eqid
    #
    wph
    @10
    @20
    cmnd
    wcel
    #
    pwsco1rhm.r
    cR
    @20
    @20
    eqid
    #
    ringmgp
    syl
    #
    pwsco1rhm.a
    pwsco1rhm.b
    pwsco1rhm.f
    pwsco1mhm
    wph
    vg
    cC
    @22
    @2
    wph
    cR
    cbs
    cfv
    #
    cB
    cmap
    co
    #
    cC
    @22
    wph
    @31
    cZ
    cbs
    cfv
    #
    cC
    wph
    @16
    @11
    @31
    @32
    wceq
    @17
    pwsco1rhm.b
    @30
    cR
    cB
    cmnd
    cW
    cZ
    pwsco1rhm.z
    @30
    eqid
    #
    pwsbas
    syl2anc
    pwsco1rhm.c
    syl6eqr
    wph
    @27
    @11
    @31
    @22
    wceq
    @29
    pwsco1rhm.b
    @30
    @20
    cB
    cmnd
    cW
    @21
    @25
    @30
    cR
    @20
    @28
    @33
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
    @21
    @23
    wph
    @34
    eqidd
    wph
    @35
    eqidd
    wph
    @34
    @22
    wceq
    #
    @6
    cplusg
    cfv
    #
    @21
    cplusg
    cfv
    #
    wceq
    #
    wph
    @10
    @11
    @36
    @39
    wa
    pwsco1rhm.r
    pwsco1rhm.b
    @34
    @22
    @37
    @38
    cR
    cB
    @20
    @6
    crg
    cW
    cZ
    @21
    pwsco1rhm.z
    @28
    @25
    @6
    eqid
    #
    @34
    eqid
    @26
    @37
    eqid
    @38
    eqid
    pwsmgp
    syl2anc
    #
    simpld
    wph
    @35
    @23
    cbs
    cfv
    #
    wceq
    #
    @7
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
    @13
    @43
    @46
    wa
    pwsco1rhm.r
    pwsco1rhm.a
    @35
    @42
    @44
    @45
    cR
    cA
    @20
    @7
    crg
    cV
    cY
    @23
    pwsco1rhm.y
    @28
    @24
    @7
    eqid
    #
    @35
    eqid
    @42
    eqid
    @44
    eqid
    @45
    eqid
    pwsmgp
    syl2anc
    #
    simpld
    wph
    vx
    cv
    #
    @34
    wcel
    vy
    cv
    #
    @34
    wcel
    wa
    vx
    vy
    @37
    @38
    wph
    @36
    @39
    @41
    simprd
    oveqdr
    wph
    @49
    @35
    wcel
    @50
    @35
    wcel
    wa
    vx
    vy
    @44
    @45
    wph
    @43
    @46
    @48
    simprd
    oveqdr
    mhmpropd
    3eltr4d
    jca
    cZ
    cY
    @3
    @6
    @7
    @40
    @47
    isrhm
    sylanbrc
end
