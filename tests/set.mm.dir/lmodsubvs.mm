include "co.mm"
include "cur.mm"
include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "lmodvsubval2.mm"
include "cmulr.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "ringgrp.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "ringnegl.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem lmodsubvs
  let wph: wff ph
  let cA: class A
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lmodsubvs.v: |- V = ( Base ` W )
  assume lmodsubvs.p: |- .+ = ( +g ` W )
  assume lmodsubvs.m: |- .- = ( -g ` W )
  assume lmodsubvs.t: |- .x. = ( .s ` W )
  assume lmodsubvs.f: |- F = ( Scalar ` W )
  assume lmodsubvs.k: |- K = ( Base ` F )
  assume lmodsubvs.n: |- N = ( invg ` F )
  assume lmodsubvs.w: |- ( ph -> W e. LMod )
  assume lmodsubvs.a: |- ( ph -> A e. K )
  assume lmodsubvs.x: |- ( ph -> X e. V )
  assume lmodsubvs.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( X .- ( A .x. Y ) ) = ( X .+ ( ( N ` A ) .x. Y ) ) )

  proof
    wph
    cX
    cA
    cY
    c.x
    co
    #
    c.mi
    co
    #
    cX
    cF
    cur
    cfv
    #
    cN
    cfv
    #
    @0
    c.x
    co
    #
    c.pl
    co
    #
    cX
    cA
    cN
    cfv
    #
    cY
    c.x
    co
    #
    c.pl
    co
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    @0
    cV
    wcel
    #
    @1
    @5
    wceq
    lmodsubvs.w
    lmodsubvs.x
    wph
    @8
    cA
    cK
    wcel
    #
    cY
    cV
    wcel
    #
    @9
    lmodsubvs.w
    lmodsubvs.a
    lmodsubvs.y
    cA
    c.x
    cF
    cK
    cV
    cW
    cY
    lmodsubvs.v
    lmodsubvs.f
    lmodsubvs.t
    lmodsubvs.k
    lmodvscl
    syl3anc
    cX
    @0
    c.pl
    c.x
    @2
    cF
    c.mi
    cN
    cV
    cW
    lmodsubvs.v
    lmodsubvs.p
    lmodsubvs.m
    lmodsubvs.f
    lmodsubvs.t
    lmodsubvs.n
    @2
    eqid
    #
    lmodvsubval2
    syl3anc
    wph
    @4
    @7
    cX
    c.pl
    wph
    @3
    cA
    cF
    cmulr
    cfv
    #
    co
    #
    cY
    c.x
    co
    #
    @4
    @7
    wph
    @8
    @3
    cK
    wcel
    #
    @10
    @11
    @15
    @4
    wceq
    lmodsubvs.w
    wph
    cF
    cgrp
    wcel
    #
    @2
    cK
    wcel
    #
    @16
    wph
    cF
    crg
    wcel
    #
    @17
    wph
    @8
    @19
    lmodsubvs.w
    cF
    cW
    lmodsubvs.f
    lmodring
    syl
    #
    cF
    ringgrp
    syl
    wph
    @19
    @18
    @20
    cK
    cF
    @2
    lmodsubvs.k
    @12
    ringidcl
    syl
    cK
    cF
    cN
    @2
    lmodsubvs.k
    lmodsubvs.n
    grpinvcl
    syl2anc
    lmodsubvs.a
    lmodsubvs.y
    @3
    cA
    c.x
    @13
    cF
    cK
    cV
    cW
    cY
    lmodsubvs.v
    lmodsubvs.f
    lmodsubvs.t
    lmodsubvs.k
    @13
    eqid
    #
    lmodvsass
    syl13anc
    wph
    @14
    @6
    cY
    c.x
    wph
    cK
    cF
    @13
    @2
    cN
    cA
    lmodsubvs.k
    @21
    @12
    lmodsubvs.n
    @20
    lmodsubvs.a
    ringnegl
    oveq1d
    eqtr3d
    oveq2d
    eqtrd
end
