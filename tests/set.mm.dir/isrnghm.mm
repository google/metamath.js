include "crngh.mm"
include "co.mm"
include "wcel.mm"
include "crng.mm"
include "wa.mm"
include "cghm.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "rnghmrcl.mm"
include "cplusg.mm"
include "cbs.mm"
include "cmap.mm"
include "crab.mm"
include "eqid.mm"
include "rnghmval.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "r19.26-2.mm"
include "anbi2i.mm"
include "anass.mm"
include "bitr4i.mm"
include "cgrp.mm"
include "wf.mm"
include "isghm.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "anbi1d.mm"
include "cabl.mm"
include "rngabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "ibar.mm"
include "syl2an.mm"
include "bitr2d.mm"
include "syl5rbb.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "biadan2.mm"

theorem isrnghm
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let c.as: class .*
  let vf: setvar f
  let vk: setvar k
  assume isrnghm.b: |- B = ( Base ` R )
  assume isrnghm.t: |- .x. = ( .r ` R )
  assume isrnghm.m: |- .* = ( .r ` S )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint F x
  disjoint F y
  disjoint B f
  disjoint f x
  disjoint f y
  disjoint R f
  disjoint S f
  disjoint F f
  disjoint .x. f
  disjoint .* f
  disjoint k x
  assert |- ( F e. ( R RngHomo S ) <-> ( ( R e. Rng /\ S e. Rng ) /\ ( F e. ( R GrpHom S ) /\ A. x e. B A. y e. B ( F ` ( x .x. y ) ) = ( ( F ` x ) .* ( F ` y ) ) ) ) )

  proof
    cF
    cR
    cS
    crngh
    co
    #
    wcel
    #
    cR
    crng
    wcel
    #
    cS
    crng
    wcel
    #
    wa
    #
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    c.as
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    cR
    cS
    cF
    rnghmrcl
    @4
    @1
    cF
    @6
    @7
    cR
    cplusg
    cfv
    #
    co
    #
    vf
    cv
    #
    cfv
    #
    @6
    @18
    cfv
    #
    @7
    @18
    cfv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    @8
    @18
    cfv
    #
    @20
    @21
    c.as
    co
    #
    wceq
    #
    wa
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    vf
    cS
    cbs
    cfv
    #
    cB
    cmap
    co
    #
    crab
    #
    wcel
    #
    @15
    @4
    @0
    @32
    cF
    vx
    vy
    cB
    @30
    @16
    @22
    cR
    cS
    c.x
    vf
    c.as
    isrnghm.b
    isrnghm.t
    isrnghm.m
    @30
    eqid
    #
    @16
    eqid
    #
    @22
    eqid
    #
    rnghmval
    eleq2d
    @33
    cF
    @31
    wcel
    #
    @17
    cF
    cfv
    #
    @10
    @11
    @22
    co
    #
    wceq
    #
    @13
    wa
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    @4
    @15
    @29
    @42
    vf
    cF
    @31
    @18
    cF
    wceq
    #
    @28
    @41
    vx
    vy
    cB
    cB
    @44
    @24
    @40
    @27
    @13
    @44
    @19
    @38
    @23
    @39
    @17
    @18
    cF
    fveq1
    @44
    @20
    @10
    @21
    @11
    @22
    @6
    @18
    cF
    fveq1
    #
    @7
    @18
    cF
    fveq1
    #
    oveq12d
    eqeq12d
    @44
    @25
    @9
    @26
    @12
    @8
    @18
    cF
    fveq1
    @44
    @20
    @10
    @21
    @11
    c.as
    @45
    @46
    oveq12d
    eqeq12d
    anbi12d
    2ralbidv
    elrab
    @43
    @37
    @40
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    @14
    wa
    #
    @4
    @15
    @43
    @37
    @47
    @14
    wa
    #
    wa
    @49
    @42
    @50
    @37
    @40
    @13
    vx
    vy
    cB
    cB
    r19.26-2
    anbi2i
    @37
    @47
    @14
    anass
    bitr4i
    @4
    @48
    @5
    @14
    @5
    cR
    cgrp
    wcel
    #
    cS
    cgrp
    wcel
    #
    wa
    #
    cB
    @30
    cF
    wf
    #
    @47
    wa
    #
    wa
    #
    @4
    @48
    vy
    vx
    @16
    @22
    cR
    cS
    cF
    cB
    @30
    isrnghm.b
    @34
    @35
    @36
    isghm
    @4
    @48
    @55
    @56
    @4
    @37
    @54
    @47
    @30
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    @37
    @54
    wb
    @4
    @57
    @58
    cS
    cbs
    fvex
    cB
    cR
    cbs
    cfv
    cvv
    isrnghm.b
    cR
    cbs
    fvex
    eqeltri
    pm3.2i
    @30
    cB
    cF
    cvv
    cvv
    elmapg
    mp1i
    anbi1d
    @2
    @51
    @52
    @55
    @56
    wb
    @3
    @2
    cR
    cabl
    wcel
    @51
    cR
    rngabl
    cR
    ablgrp
    syl
    @3
    cS
    cabl
    wcel
    @52
    cS
    rngabl
    cS
    ablgrp
    syl
    @53
    @55
    ibar
    syl2an
    bitr2d
    syl5rbb
    anbi1d
    syl5bb
    syl5bb
    bitrd
    biadan2
end
