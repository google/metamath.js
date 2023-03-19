include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cplusg.mm"
include "c0g.mm"
include "crg.mm"
include "wcel.mm"
include "ringidcl.mm"
include "syl.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "ringdir.mm"
include "syl13anc.mm"
include "grprinv.mm"
include "oveq1d.mm"
include "ringlz.mm"
include "eqtrd.mm"
include "ringlidm.mm"
include "3eqtr3rd.mm"
include "wb.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "grpinvid1.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem ringnegl
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


  assert |- ( ph -> ( ( N ` .1. ) .x. X ) = ( N ` X ) )

  proof
    wph
    cX
    cN
    cfv
    #
    c.1
    cN
    cfv
    #
    cX
    c.x
    co
    #
    wph
    @0
    @2
    wceq
    #
    cX
    @2
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
    c.1
    @1
    @4
    co
    #
    cX
    c.x
    co
    #
    c.1
    cX
    c.x
    co
    #
    @2
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
    c.1
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    cX
    cB
    wcel
    #
    @9
    @11
    wceq
    ringnegl.r
    wph
    @12
    @13
    ringnegl.r
    cB
    cR
    c.1
    ringnegl.b
    ringnegl.u
    ringidcl
    syl
    #
    wph
    cR
    cgrp
    wcel
    #
    @13
    @14
    wph
    @12
    @17
    ringnegl.r
    cR
    ringgrp
    syl
    #
    @16
    cB
    cR
    cN
    c.1
    ringnegl.b
    ringnegl.n
    grpinvcl
    syl2anc
    #
    ringnegl.x
    cB
    @4
    cR
    c.x
    c.1
    @1
    cX
    ringnegl.b
    @4
    eqid
    #
    ringnegl.t
    ringdir
    syl13anc
    wph
    @9
    @6
    cX
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
    @17
    @13
    @8
    @6
    wceq
    @18
    @16
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
    grprinv
    syl2anc
    oveq1d
    wph
    @12
    @15
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
    ringlz
    syl2anc
    eqtrd
    wph
    @10
    cX
    @2
    @4
    wph
    @12
    @15
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
    ringlidm
    syl2anc
    oveq1d
    3eqtr3rd
    wph
    @17
    @15
    @2
    cB
    wcel
    #
    @3
    @7
    wb
    @18
    ringnegl.x
    wph
    @12
    @14
    @15
    @23
    ringnegl.r
    @19
    ringnegl.x
    cB
    cR
    c.x
    @1
    cX
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
    grpinvid1
    syl3anc
    mpbird
    eqcomd
end
