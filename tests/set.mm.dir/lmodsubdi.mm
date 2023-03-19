include "co.mm"
include "cur.mm"
include "cfv.mm"
include "cminusg.mm"
include "cplusg.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "lmodvsubval2.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "cmulr.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "rngnegr.mm"
include "ringnegl.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"
include "lmodvscl.mm"
include "lmodvsdi.mm"
include "3eqtr4rd.mm"

theorem lmodsubdi
  let wph: wff ph
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lmodsubdi.v: |- V = ( Base ` W )
  assume lmodsubdi.t: |- .x. = ( .s ` W )
  assume lmodsubdi.f: |- F = ( Scalar ` W )
  assume lmodsubdi.k: |- K = ( Base ` F )
  assume lmodsubdi.m: |- .- = ( -g ` W )
  assume lmodsubdi.w: |- ( ph -> W e. LMod )
  assume lmodsubdi.a: |- ( ph -> A e. K )
  assume lmodsubdi.x: |- ( ph -> X e. V )
  assume lmodsubdi.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( A .x. ( X .- Y ) ) = ( ( A .x. X ) .- ( A .x. Y ) ) )

  proof
    wph
    cA
    cX
    cY
    c.mi
    co
    #
    c.x
    co
    cA
    cX
    cF
    cur
    cfv
    #
    cF
    cminusg
    cfv
    #
    cfv
    #
    cY
    c.x
    co
    #
    cW
    cplusg
    cfv
    #
    co
    #
    c.x
    co
    #
    cA
    cX
    c.x
    co
    #
    cA
    cY
    c.x
    co
    #
    c.mi
    co
    #
    wph
    @0
    @6
    cA
    c.x
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @0
    @6
    wceq
    lmodsubdi.w
    lmodsubdi.x
    lmodsubdi.y
    cX
    cY
    @5
    c.x
    @1
    cF
    c.mi
    @2
    cV
    cW
    lmodsubdi.v
    @5
    eqid
    #
    lmodsubdi.m
    lmodsubdi.f
    lmodsubdi.t
    @2
    eqid
    #
    @1
    eqid
    #
    lmodvsubval2
    syl3anc
    oveq2d
    wph
    @8
    cA
    @4
    c.x
    co
    #
    @5
    co
    #
    @8
    @3
    @9
    c.x
    co
    #
    @5
    co
    #
    @7
    @10
    wph
    @17
    @19
    @8
    @5
    wph
    cA
    @3
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
    @3
    cA
    @21
    co
    #
    cY
    c.x
    co
    #
    @17
    @19
    wph
    @22
    @24
    cY
    c.x
    wph
    @22
    cA
    @2
    cfv
    @24
    wph
    cK
    cF
    @21
    @1
    @2
    cA
    lmodsubdi.k
    @21
    eqid
    #
    @16
    @15
    wph
    @11
    cF
    crg
    wcel
    #
    lmodsubdi.w
    cF
    cW
    lmodsubdi.f
    lmodring
    syl
    #
    lmodsubdi.a
    rngnegr
    wph
    cK
    cF
    @21
    @1
    @2
    cA
    lmodsubdi.k
    @26
    @16
    @15
    @28
    lmodsubdi.a
    ringnegl
    eqtr4d
    oveq1d
    wph
    @11
    cA
    cK
    wcel
    #
    @3
    cK
    wcel
    #
    @13
    @23
    @17
    wceq
    lmodsubdi.w
    lmodsubdi.a
    wph
    cF
    cgrp
    wcel
    #
    @1
    cK
    wcel
    #
    @30
    wph
    @27
    @31
    @28
    cF
    ringgrp
    syl
    wph
    @27
    @32
    @28
    cK
    cF
    @1
    lmodsubdi.k
    @16
    ringidcl
    syl
    cK
    cF
    @2
    @1
    lmodsubdi.k
    @15
    grpinvcl
    syl2anc
    #
    lmodsubdi.y
    cA
    @3
    c.x
    @21
    cF
    cK
    cV
    cW
    cY
    lmodsubdi.v
    lmodsubdi.f
    lmodsubdi.t
    lmodsubdi.k
    @26
    lmodvsass
    syl13anc
    wph
    @11
    @30
    @29
    @13
    @25
    @19
    wceq
    lmodsubdi.w
    @33
    lmodsubdi.a
    lmodsubdi.y
    @3
    cA
    c.x
    @21
    cF
    cK
    cV
    cW
    cY
    lmodsubdi.v
    lmodsubdi.f
    lmodsubdi.t
    lmodsubdi.k
    @26
    lmodvsass
    syl13anc
    3eqtr3d
    oveq2d
    wph
    @11
    @29
    @12
    @4
    cV
    wcel
    #
    @7
    @18
    wceq
    lmodsubdi.w
    lmodsubdi.a
    lmodsubdi.x
    wph
    @11
    @30
    @13
    @34
    lmodsubdi.w
    @33
    lmodsubdi.y
    @3
    c.x
    cF
    cK
    cV
    cW
    cY
    lmodsubdi.v
    lmodsubdi.f
    lmodsubdi.t
    lmodsubdi.k
    lmodvscl
    syl3anc
    @5
    cA
    c.x
    cF
    cK
    cV
    cW
    cX
    @4
    lmodsubdi.v
    @14
    lmodsubdi.f
    lmodsubdi.t
    lmodsubdi.k
    lmodvsdi
    syl13anc
    wph
    @11
    @8
    cV
    wcel
    #
    @9
    cV
    wcel
    #
    @10
    @20
    wceq
    lmodsubdi.w
    wph
    @11
    @29
    @12
    @35
    lmodsubdi.w
    lmodsubdi.a
    lmodsubdi.x
    cA
    c.x
    cF
    cK
    cV
    cW
    cX
    lmodsubdi.v
    lmodsubdi.f
    lmodsubdi.t
    lmodsubdi.k
    lmodvscl
    syl3anc
    wph
    @11
    @29
    @13
    @36
    lmodsubdi.w
    lmodsubdi.a
    lmodsubdi.y
    cA
    c.x
    cF
    cK
    cV
    cW
    cY
    lmodsubdi.v
    lmodsubdi.f
    lmodsubdi.t
    lmodsubdi.k
    lmodvscl
    syl3anc
    @8
    @9
    @5
    c.x
    @1
    cF
    c.mi
    @2
    cV
    cW
    lmodsubdi.v
    @14
    lmodsubdi.m
    lmodsubdi.f
    lmodsubdi.t
    @15
    @16
    lmodvsubval2
    syl3anc
    3eqtr4rd
    eqtr4d
end
