include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cplusg.mm"
include "c0g.mm"
include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "ringdi.mm"
include "syl13anc.mm"
include "grplinv.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "eqtrd.mm"
include "ringridm.mm"
include "3eqtr3rd.mm"
include "wb.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "grpinvid2.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem rngnegr
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cN: class N
  let cX: class X
  assume ringnegl.b: |- B = ( Base ` R )
  assume ringnegl.t: |- .x. = ( .r ` R )
  assume ringnegl.u: |- .1. = ( 1r ` R )
  assume ringnegl.n: |- N = ( invg ` R )
  assume ringnegl.r: |- ( ph -> R e. Ring )
  assume ringnegl.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( X .x. ( N ` .1. ) ) = ( N ` X ) )

  proof
    wph
    cX
    cN
    cfv
    #
    cX
    c.1
    cN
    cfv
    #
    c.x
    co
    #
    wph
    @0
    @2
    wceq
    #
    @2
    cX
    cR
    cplusg
    cfv
    #
    co
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wph
    cX
    @1
    c.1
    @4
    co
    #
    c.x
    co
    #
    @2
    cX
    c.1
    c.x
    co
    #
    @4
    co
    #
    @6
    @5
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
    c.1
    cB
    wcel
    #
    @9
    @11
    wceq
    ringnegl.r
    ringnegl.x
    wph
    cR
    cgrp
    wcel
    #
    @15
    @14
    wph
    @12
    @16
    ringnegl.r
    cR
    ringgrp
    syl
    #
    wph
    @12
    @15
    ringnegl.r
    cB
    cR
    c.1
    ringnegl.b
    ringnegl.u
    ringidcl
    syl
    #
    cB
    cR
    cN
    c.1
    ringnegl.b
    ringnegl.n
    grpinvcl
    syl2anc
    #
    @18
    cB
    @4
    cR
    c.x
    cX
    @1
    c.1
    ringnegl.b
    @4
    eqid
    #
    ringnegl.t
    ringdi
    syl13anc
    wph
    @9
    cX
    @6
    c.x
    co
    #
    @6
    wph
    @8
    @6
    cX
    c.x
    wph
    @16
    @15
    @8
    @6
    wceq
    @17
    @18
    cB
    @4
    cR
    cN
    c.1
    @6
    ringnegl.b
    @20
    @6
    eqid
    #
    ringnegl.n
    grplinv
    syl2anc
    oveq2d
    wph
    @12
    @13
    @21
    @6
    wceq
    ringnegl.r
    ringnegl.x
    cB
    cR
    c.x
    cX
    @6
    ringnegl.b
    ringnegl.t
    @22
    ringrz
    syl2anc
    eqtrd
    wph
    @10
    cX
    @2
    @4
    wph
    @12
    @13
    @10
    cX
    wceq
    ringnegl.r
    ringnegl.x
    cB
    cR
    c.x
    c.1
    cX
    ringnegl.b
    ringnegl.t
    ringnegl.u
    ringridm
    syl2anc
    oveq2d
    3eqtr3rd
    wph
    @16
    @13
    @2
    cB
    wcel
    #
    @3
    @7
    wb
    @17
    ringnegl.x
    wph
    @12
    @13
    @14
    @23
    ringnegl.r
    ringnegl.x
    @19
    cB
    cR
    c.x
    cX
    @1
    ringnegl.b
    ringnegl.t
    ringcl
    syl3anc
    cB
    @4
    cR
    cN
    cX
    @2
    @6
    ringnegl.b
    @20
    @22
    ringnegl.n
    grpinvid2
    syl3anc
    mpbird
    eqcomd
end
