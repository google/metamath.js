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
include "ringdi.mm"
include "syl13anc.mm"
include "ringmneg2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "grpsubval.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem ringsubdi
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


  assert |- ( ph -> ( X .x. ( Y .- Z ) ) = ( ( X .x. Y ) .- ( X .x. Z ) ) )

  proof
    wph
    cX
    cY
    cZ
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
    c.x
    co
    #
    cX
    cY
    c.x
    co
    #
    cX
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
    cZ
    c.mi
    co
    #
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
    cX
    @1
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
    cY
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @4
    @12
    wceq
    ringsubdi.r
    ringsubdi.x
    ringsubdi.y
    wph
    cR
    cgrp
    wcel
    #
    cZ
    cB
    wcel
    #
    @16
    wph
    @13
    @17
    ringsubdi.r
    cR
    ringgrp
    syl
    ringsubdi.z
    cB
    cR
    @0
    cZ
    ringsubdi.b
    @0
    eqid
    #
    grpinvcl
    syl2anc
    cB
    @2
    cR
    c.x
    cX
    cY
    @1
    ringsubdi.b
    @2
    eqid
    #
    ringsubdi.t
    ringdi
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
    cX
    cZ
    ringsubdi.b
    ringsubdi.t
    @19
    ringsubdi.r
    ringsubdi.x
    ringsubdi.z
    ringmneg2
    oveq2d
    eqtrd
    wph
    @9
    @3
    cX
    c.x
    wph
    @15
    @18
    @9
    @3
    wceq
    ringsubdi.y
    ringsubdi.z
    cB
    @2
    cR
    @0
    c.mi
    cY
    cZ
    ringsubdi.b
    @20
    @19
    ringsubdi.m
    grpsubval
    syl2anc
    oveq2d
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
    @15
    @21
    ringsubdi.r
    ringsubdi.x
    ringsubdi.y
    cB
    cR
    c.x
    cX
    cY
    ringsubdi.b
    ringsubdi.t
    ringcl
    syl3anc
    wph
    @13
    @14
    @18
    @22
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
