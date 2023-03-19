include "cur.mm"
include "cfv.mm"
include "co.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "eqid.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringnegl.mm"
include "oveq1d.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "3eqtr3d.mm"

theorem ringmneg1
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cX: class X
  let cY: class Y
  assume ringneglmul.b: |- B = ( Base ` R )
  assume ringneglmul.t: |- .x. = ( .r ` R )
  assume ringneglmul.n: |- N = ( invg ` R )
  assume ringneglmul.r: |- ( ph -> R e. Ring )
  assume ringneglmul.x: |- ( ph -> X e. B )
  assume ringneglmul.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( N ` X ) .x. Y ) = ( N ` ( X .x. Y ) ) )

  proof
    wph
    cR
    cur
    cfv
    #
    cN
    cfv
    #
    cX
    c.x
    co
    #
    cY
    c.x
    co
    #
    @1
    cX
    cY
    c.x
    co
    #
    c.x
    co
    #
    cX
    cN
    cfv
    #
    cY
    c.x
    co
    @4
    cN
    cfv
    wph
    cR
    crg
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
    cY
    cB
    wcel
    #
    @3
    @5
    wceq
    ringneglmul.r
    wph
    cR
    cgrp
    wcel
    #
    @0
    cB
    wcel
    #
    @8
    wph
    @7
    @11
    ringneglmul.r
    cR
    ringgrp
    syl
    wph
    @7
    @12
    ringneglmul.r
    cB
    cR
    @0
    ringneglmul.b
    @0
    eqid
    #
    ringidcl
    syl
    cB
    cR
    cN
    @0
    ringneglmul.b
    ringneglmul.n
    grpinvcl
    syl2anc
    ringneglmul.x
    ringneglmul.y
    cB
    cR
    c.x
    @1
    cX
    cY
    ringneglmul.b
    ringneglmul.t
    ringass
    syl13anc
    wph
    @2
    @6
    cY
    c.x
    wph
    cB
    cR
    c.x
    @0
    cN
    cX
    ringneglmul.b
    ringneglmul.t
    @13
    ringneglmul.n
    ringneglmul.r
    ringneglmul.x
    ringnegl
    oveq1d
    wph
    cB
    cR
    c.x
    @0
    cN
    @4
    ringneglmul.b
    ringneglmul.t
    @13
    ringneglmul.n
    ringneglmul.r
    wph
    @7
    @9
    @10
    @4
    cB
    wcel
    ringneglmul.r
    ringneglmul.x
    ringneglmul.y
    cB
    cR
    c.x
    cX
    cY
    ringneglmul.b
    ringneglmul.t
    ringcl
    syl3anc
    ringnegl
    3eqtr3d
end
