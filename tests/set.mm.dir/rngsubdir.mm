include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ringdir.mm"
include "syl13anc.mm"
include "ringmneg1.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "grpsubval.mm"
include "oveq1d.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem rngsubdir
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ringsubdi.b: |- B = ( Base ` R )
  assume ringsubdi.t: |- .x. = ( .r ` R )
  assume ringsubdi.m: |- .- = ( -g ` R )
  assume ringsubdi.r: |- ( ph -> R e. Ring )
  assume ringsubdi.x: |- ( ph -> X e. B )
  assume ringsubdi.y: |- ( ph -> Y e. B )
  assume ringsubdi.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( ( X .- Y ) .x. Z ) = ( ( X .x. Z ) .- ( Y .x. Z ) ) )

  proof
    wph
    cX
    cY
    cR
    cminusg
    cfv
    #
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    cZ
    c.x
    co
    #
    cX
    cZ
    c.x
    co
    #
    cY
    cZ
    c.x
    co
    #
    @0
    cfv
    #
    @2
    co
    #
    cX
    cY
    c.mi
    co
    #
    cZ
    c.x
    co
    @5
    @6
    c.mi
    co
    #
    wph
    @4
    @5
    @1
    cZ
    c.x
    co
    #
    @2
    co
    #
    @8
    wph
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    @4
    @12
    wceq
    ringsubdi.r
    ringsubdi.x
    wph
    cR
    cgrp
    wcel
    #
    cY
    cB
    wcel
    #
    @15
    wph
    @13
    @17
    ringsubdi.r
    cR
    ringgrp
    syl
    ringsubdi.y
    cB
    cR
    @0
    cY
    ringsubdi.b
    @0
    eqid
    #
    grpinvcl
    syl2anc
    ringsubdi.z
    cB
    @2
    cR
    c.x
    cX
    @1
    cZ
    ringsubdi.b
    @2
    eqid
    #
    ringsubdi.t
    ringdir
    syl13anc
    wph
    @11
    @7
    @5
    @2
    wph
    cB
    cR
    c.x
    @0
    cY
    cZ
    ringsubdi.b
    ringsubdi.t
    @19
    ringsubdi.r
    ringsubdi.y
    ringsubdi.z
    ringmneg1
    oveq2d
    eqtrd
    wph
    @9
    @3
    cZ
    c.x
    wph
    @14
    @18
    @9
    @3
    wceq
    ringsubdi.x
    ringsubdi.y
    cB
    @2
    cR
    @0
    c.mi
    cX
    cY
    ringsubdi.b
    @20
    @19
    ringsubdi.m
    grpsubval
    syl2anc
    oveq1d
    wph
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @10
    @8
    wceq
    wph
    @13
    @14
    @16
    @21
    ringsubdi.r
    ringsubdi.x
    ringsubdi.z
    cB
    cR
    c.x
    cX
    cZ
    ringsubdi.b
    ringsubdi.t
    ringcl
    syl3anc
    wph
    @13
    @18
    @16
    @22
    ringsubdi.r
    ringsubdi.y
    ringsubdi.z
    cB
    cR
    c.x
    cY
    cZ
    ringsubdi.b
    ringsubdi.t
    ringcl
    syl3anc
    cB
    @2
    cR
    @0
    c.mi
    @5
    @6
    ringsubdi.b
    @20
    @19
    ringsubdi.m
    grpsubval
    syl2anc
    3eqtr4d
end
