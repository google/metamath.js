include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "ctgp.mm"
include "wcel.mm"
include "ctps.mm"
include "tgptps.mm"
include "syl.mm"
include "cghm.mm"
include "co.mm"
include "cmhm.mm"
include "cabl.mm"
include "cgrp.mm"
include "ccmn.mm"
include "tgpgrp.mm"
include "isabl.mm"
include "sylanbrc.mm"
include "invghm.mm"
include "sylib.mm"
include "ghmmhm.mm"
include "ccn.mm"
include "tgpinv.mm"
include "tsmsmhm.mm"

theorem tsmsinv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  assume tsmsinv.b: |- B = ( Base ` G )
  assume tsmsinv.p: |- I = ( invg ` G )
  assume tsmsinv.1: |- ( ph -> G e. CMnd )
  assume tsmsinv.2: |- ( ph -> G e. TopGrp )
  assume tsmsinv.a: |- ( ph -> A e. V )
  assume tsmsinv.f: |- ( ph -> F : A --> B )
  assume tsmsinv.x: |- ( ph -> X e. ( G tsums F ) )


  assert |- ( ph -> ( I ` X ) e. ( G tsums ( I o. F ) ) )

  proof
    wph
    cA
    cB
    cI
    cF
    cG
    cG
    cG
    ctopn
    cfv
    #
    @0
    cV
    cX
    tsmsinv.b
    @0
    eqid
    #
    @1
    tsmsinv.1
    wph
    cG
    ctgp
    wcel
    #
    cG
    ctps
    wcel
    tsmsinv.2
    cG
    tgptps
    syl
    #
    tsmsinv.1
    @3
    wph
    cI
    cG
    cG
    cghm
    co
    wcel
    #
    cI
    cG
    cG
    cmhm
    co
    wcel
    wph
    cG
    cabl
    wcel
    #
    @4
    wph
    cG
    cgrp
    wcel
    #
    cG
    ccmn
    wcel
    @5
    wph
    @2
    @6
    tsmsinv.2
    cG
    tgpgrp
    syl
    tsmsinv.1
    cG
    isabl
    sylanbrc
    cB
    cG
    cI
    tsmsinv.b
    tsmsinv.p
    invghm
    sylib
    cG
    cG
    cI
    ghmmhm
    syl
    wph
    @2
    cI
    @0
    @0
    ccn
    co
    wcel
    tsmsinv.2
    cG
    cI
    @0
    @1
    tsmsinv.p
    tgpinv
    syl
    tsmsinv.a
    tsmsinv.f
    tsmsinv.x
    tsmsmhm
end
