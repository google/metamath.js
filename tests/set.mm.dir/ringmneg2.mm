include "co.mm"
include "cur.mm"
include "cfv.mm"
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
include "ringcl.mm"
include "syl3anc.mm"
include "rngnegr.mm"
include "oveq2d.mm"
include "3eqtr3rd.mm"

theorem ringmneg2
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


  assert |- ( ph -> ( X .x. ( N ` Y ) ) = ( N ` ( X .x. Y ) ) )

  proof
    wph
    cX
    cY
    c.x
    co
    #
    cR
    cur
    cfv
    #
    cN
    cfv
    #
    c.x
    co
    #
    cX
    cY
    @2
    c.x
    co
    #
    c.x
    co
    #
    @0
    cN
    cfv
    cX
    cY
    cN
    cfv
    #
    c.x
    co
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
    @2
    cB
    wcel
    #
    @3
    @5
    wceq
    ringneglmul.r
    ringneglmul.x
    ringneglmul.y
    wph
    cR
    cgrp
    wcel
    #
    @1
    cB
    wcel
    #
    @10
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
    @1
    ringneglmul.b
    @1
    eqid
    #
    ringidcl
    syl
    cB
    cR
    cN
    @1
    ringneglmul.b
    ringneglmul.n
    grpinvcl
    syl2anc
    cB
    cR
    c.x
    cX
    cY
    @2
    ringneglmul.b
    ringneglmul.t
    ringass
    syl13anc
    wph
    cB
    cR
    c.x
    @1
    cN
    @0
    ringneglmul.b
    ringneglmul.t
    @13
    ringneglmul.n
    ringneglmul.r
    wph
    @7
    @8
    @9
    @0
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
    rngnegr
    wph
    @4
    @6
    cX
    c.x
    wph
    cB
    cR
    c.x
    @1
    cN
    cY
    ringneglmul.b
    ringneglmul.t
    @13
    ringneglmul.n
    ringneglmul.r
    ringneglmul.y
    rngnegr
    oveq2d
    3eqtr3rd
end
