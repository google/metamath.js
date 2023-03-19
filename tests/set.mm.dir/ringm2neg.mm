include "cfv.mm"
include "co.mm"
include "cgrp.mm"
include "wcel.mm"
include "crg.mm"
include "ringgrp.mm"
include "syl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ringmneg1.mm"
include "ringmneg2.mm"
include "fveq2d.mm"
include "wceq.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "grpinvinv.mm"
include "3eqtrd.mm"

theorem ringm2neg
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


  assert |- ( ph -> ( ( N ` X ) .x. ( N ` Y ) ) = ( X .x. Y ) )

  proof
    wph
    cX
    cN
    cfv
    cY
    cN
    cfv
    #
    c.x
    co
    cX
    @0
    c.x
    co
    #
    cN
    cfv
    cX
    cY
    c.x
    co
    #
    cN
    cfv
    #
    cN
    cfv
    #
    @2
    wph
    cB
    cR
    c.x
    cN
    cX
    @0
    ringneglmul.b
    ringneglmul.t
    ringneglmul.n
    ringneglmul.r
    ringneglmul.x
    wph
    cR
    cgrp
    wcel
    #
    cY
    cB
    wcel
    #
    @0
    cB
    wcel
    wph
    cR
    crg
    wcel
    #
    @5
    ringneglmul.r
    cR
    ringgrp
    syl
    #
    ringneglmul.y
    cB
    cR
    cN
    cY
    ringneglmul.b
    ringneglmul.n
    grpinvcl
    syl2anc
    ringmneg1
    wph
    @1
    @3
    cN
    wph
    cB
    cR
    c.x
    cN
    cX
    cY
    ringneglmul.b
    ringneglmul.t
    ringneglmul.n
    ringneglmul.r
    ringneglmul.x
    ringneglmul.y
    ringmneg2
    fveq2d
    wph
    @5
    @2
    cB
    wcel
    #
    @4
    @2
    wceq
    @8
    wph
    @7
    cX
    cB
    wcel
    @6
    @9
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
    cB
    cR
    cN
    @2
    ringneglmul.b
    ringneglmul.n
    grpinvinv
    syl2anc
    3eqtrd
end
