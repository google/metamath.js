include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "cur.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "ringgrp.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lmodvsdir.mm"
include "syl13anc.mm"
include "cmulr.mm"
include "ringnegl.mm"
include "oveq1d.mm"
include "ringidcl.mm"
include "lmodvsass.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "grpsubval.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmodvsubval2.mm"
include "3eqtr4d.mm"

theorem lmodsubdir
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let cX: class X
  assume lmodsubdir.v: |- V = ( Base ` W )
  assume lmodsubdir.t: |- .x. = ( .s ` W )
  assume lmodsubdir.f: |- F = ( Scalar ` W )
  assume lmodsubdir.k: |- K = ( Base ` F )
  assume lmodsubdir.m: |- .- = ( -g ` W )
  assume lmodsubdir.s: |- S = ( -g ` F )
  assume lmodsubdir.w: |- ( ph -> W e. LMod )
  assume lmodsubdir.a: |- ( ph -> A e. K )
  assume lmodsubdir.b: |- ( ph -> B e. K )
  assume lmodsubdir.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( A S B ) .x. X ) = ( ( A .x. X ) .- ( B .x. X ) ) )

  proof
    wph
    cA
    cB
    cF
    cminusg
    cfv
    #
    cfv
    #
    cF
    cplusg
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    cA
    cX
    c.x
    co
    #
    cF
    cur
    cfv
    #
    @0
    cfv
    #
    cB
    cX
    c.x
    co
    #
    c.x
    co
    #
    cW
    cplusg
    cfv
    #
    co
    #
    cA
    cB
    cS
    co
    #
    cX
    c.x
    co
    @5
    @8
    c.mi
    co
    #
    wph
    @4
    @5
    @1
    cX
    c.x
    co
    #
    @10
    co
    #
    @11
    wph
    cW
    clmod
    wcel
    #
    cA
    cK
    wcel
    #
    @1
    cK
    wcel
    #
    cX
    cV
    wcel
    #
    @4
    @15
    wceq
    lmodsubdir.w
    lmodsubdir.a
    wph
    cF
    cgrp
    wcel
    #
    cB
    cK
    wcel
    #
    @18
    wph
    cF
    crg
    wcel
    #
    @20
    wph
    @16
    @22
    lmodsubdir.w
    cF
    cW
    lmodsubdir.f
    lmodring
    syl
    #
    cF
    ringgrp
    syl
    #
    lmodsubdir.b
    cK
    cF
    @0
    cB
    lmodsubdir.k
    @0
    eqid
    #
    grpinvcl
    syl2anc
    lmodsubdir.x
    @10
    @2
    cA
    @1
    c.x
    cF
    cK
    cV
    cW
    cX
    lmodsubdir.v
    @10
    eqid
    #
    lmodsubdir.f
    lmodsubdir.t
    lmodsubdir.k
    @2
    eqid
    #
    lmodvsdir
    syl13anc
    wph
    @14
    @9
    @5
    @10
    wph
    @7
    cB
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
    @14
    @9
    wph
    @29
    @1
    cX
    c.x
    wph
    cK
    cF
    @28
    @6
    @0
    cB
    lmodsubdir.k
    @28
    eqid
    #
    @6
    eqid
    #
    @25
    @23
    lmodsubdir.b
    ringnegl
    oveq1d
    wph
    @16
    @7
    cK
    wcel
    #
    @21
    @19
    @30
    @9
    wceq
    lmodsubdir.w
    wph
    @20
    @6
    cK
    wcel
    #
    @33
    @24
    wph
    @22
    @34
    @23
    cK
    cF
    @6
    lmodsubdir.k
    @32
    ringidcl
    syl
    cK
    cF
    @0
    @6
    lmodsubdir.k
    @25
    grpinvcl
    syl2anc
    lmodsubdir.b
    lmodsubdir.x
    @7
    cB
    c.x
    @28
    cF
    cK
    cV
    cW
    cX
    lmodsubdir.v
    lmodsubdir.f
    lmodsubdir.t
    lmodsubdir.k
    @31
    lmodvsass
    syl13anc
    eqtr3d
    oveq2d
    eqtrd
    wph
    @12
    @3
    cX
    c.x
    wph
    @17
    @21
    @12
    @3
    wceq
    lmodsubdir.a
    lmodsubdir.b
    cK
    @2
    cF
    @0
    cS
    cA
    cB
    lmodsubdir.k
    @27
    @25
    lmodsubdir.s
    grpsubval
    syl2anc
    oveq1d
    wph
    @16
    @5
    cV
    wcel
    #
    @8
    cV
    wcel
    #
    @13
    @11
    wceq
    lmodsubdir.w
    wph
    @16
    @17
    @19
    @35
    lmodsubdir.w
    lmodsubdir.a
    lmodsubdir.x
    cA
    c.x
    cF
    cK
    cV
    cW
    cX
    lmodsubdir.v
    lmodsubdir.f
    lmodsubdir.t
    lmodsubdir.k
    lmodvscl
    syl3anc
    wph
    @16
    @21
    @19
    @36
    lmodsubdir.w
    lmodsubdir.b
    lmodsubdir.x
    cB
    c.x
    cF
    cK
    cV
    cW
    cX
    lmodsubdir.v
    lmodsubdir.f
    lmodsubdir.t
    lmodsubdir.k
    lmodvscl
    syl3anc
    @5
    @8
    @10
    c.x
    @6
    cF
    c.mi
    @0
    cV
    cW
    lmodsubdir.v
    @26
    lmodsubdir.m
    lmodsubdir.f
    lmodsubdir.t
    @25
    @32
    lmodvsubval2
    syl3anc
    3eqtr4d
end
