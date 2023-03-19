include "cur.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "ringgrp.mm"
include "eqid.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "ringnegl.mm"
include "oveq1d.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmodvneg1.mm"
include "3eqtr3rd.mm"

theorem lmodvsneg
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume lmodvsneg.b: |- B = ( Base ` W )
  assume lmodvsneg.f: |- F = ( Scalar ` W )
  assume lmodvsneg.s: |- .x. = ( .s ` W )
  assume lmodvsneg.n: |- N = ( invg ` W )
  assume lmodvsneg.k: |- K = ( Base ` F )
  assume lmodvsneg.m: |- M = ( invg ` F )
  assume lmodvsneg.w: |- ( ph -> W e. LMod )
  assume lmodvsneg.x: |- ( ph -> X e. B )
  assume lmodvsneg.r: |- ( ph -> R e. K )


  assert |- ( ph -> ( N ` ( R .x. X ) ) = ( ( M ` R ) .x. X ) )

  proof
    wph
    cF
    cur
    cfv
    #
    cM
    cfv
    #
    cR
    cF
    cmulr
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    @1
    cR
    cX
    c.x
    co
    #
    c.x
    co
    #
    cR
    cM
    cfv
    #
    cX
    c.x
    co
    @5
    cN
    cfv
    #
    wph
    cW
    clmod
    wcel
    #
    @1
    cK
    wcel
    #
    cR
    cK
    wcel
    #
    cX
    cB
    wcel
    #
    @4
    @6
    wceq
    lmodvsneg.w
    wph
    cF
    cgrp
    wcel
    #
    @0
    cK
    wcel
    #
    @10
    wph
    cF
    crg
    wcel
    #
    @13
    wph
    @9
    @15
    lmodvsneg.w
    cF
    cW
    lmodvsneg.f
    lmodring
    syl
    #
    cF
    ringgrp
    syl
    wph
    @15
    @14
    @16
    cK
    cF
    @0
    lmodvsneg.k
    @0
    eqid
    #
    ringidcl
    syl
    cK
    cF
    cM
    @0
    lmodvsneg.k
    lmodvsneg.m
    grpinvcl
    syl2anc
    lmodvsneg.r
    lmodvsneg.x
    @1
    cR
    c.x
    @2
    cF
    cK
    cB
    cW
    cX
    lmodvsneg.b
    lmodvsneg.f
    lmodvsneg.s
    lmodvsneg.k
    @2
    eqid
    #
    lmodvsass
    syl13anc
    wph
    @3
    @7
    cX
    c.x
    wph
    cK
    cF
    @2
    @0
    cM
    cR
    lmodvsneg.k
    @18
    @17
    lmodvsneg.m
    @16
    lmodvsneg.r
    ringnegl
    oveq1d
    wph
    @9
    @5
    cB
    wcel
    #
    @6
    @8
    wceq
    lmodvsneg.w
    wph
    @9
    @11
    @12
    @19
    lmodvsneg.w
    lmodvsneg.r
    lmodvsneg.x
    cR
    c.x
    cF
    cK
    cB
    cW
    cX
    lmodvsneg.b
    lmodvsneg.f
    lmodvsneg.s
    lmodvsneg.k
    lmodvscl
    syl3anc
    c.x
    @0
    cF
    cM
    cN
    cB
    cW
    @5
    lmodvsneg.b
    lmodvsneg.n
    lmodvsneg.f
    lmodvsneg.s
    @17
    lmodvsneg.m
    lmodvneg1
    syl2anc
    3eqtr3rd
end
