include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "ccom.mm"
include "cof.mm"
include "ctsu.mm"
include "eqid.mm"
include "ctgp.mm"
include "wcel.mm"
include "ctmd.mm"
include "tgptmd.mm"
include "syl.mm"
include "wf.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "grpinvf.mm"
include "3syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "tsmsinv.mm"
include "tsmsadd.mm"
include "wceq.mm"
include "ctps.mm"
include "tgptps.mm"
include "tsmscl.mm"
include "sseldd.mm"
include "grpsubval.mm"
include "cv.mm"
include "cmpt.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "offval2.mm"
include "cvv.mm"
include "fvexd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "3eltr4d.mm"

theorem tsmssub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume tsmssub.b: |- B = ( Base ` G )
  assume tsmssub.p: |- .- = ( -g ` G )
  assume tsmssub.1: |- ( ph -> G e. CMnd )
  assume tsmssub.2: |- ( ph -> G e. TopGrp )
  assume tsmssub.a: |- ( ph -> A e. V )
  assume tsmssub.f: |- ( ph -> F : A --> B )
  assume tsmssub.h: |- ( ph -> H : A --> B )
  assume tsmssub.x: |- ( ph -> X e. ( G tsums F ) )
  assume tsmssub.y: |- ( ph -> Y e. ( G tsums H ) )


  assert |- ( ph -> ( X .- Y ) e. ( G tsums ( F oF .- H ) ) )

  proof
    wph
    cX
    cY
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    cF
    @0
    cH
    ccom
    #
    @2
    cof
    co
    #
    ctsu
    co
    cX
    cY
    c.mi
    co
    #
    cG
    cF
    cH
    c.mi
    cof
    co
    #
    ctsu
    co
    wph
    cA
    cB
    @2
    cF
    cG
    @4
    cV
    cX
    @1
    tsmssub.b
    @2
    eqid
    #
    tsmssub.1
    wph
    cG
    ctgp
    wcel
    #
    cG
    ctmd
    wcel
    tsmssub.2
    cG
    tgptmd
    syl
    tsmssub.a
    tsmssub.f
    wph
    cB
    cB
    @0
    wf
    #
    cA
    cB
    cH
    wf
    cA
    cB
    @4
    wf
    wph
    @9
    cG
    cgrp
    wcel
    @10
    tsmssub.2
    cG
    tgpgrp
    cB
    cG
    @0
    tsmssub.b
    @0
    eqid
    #
    grpinvf
    3syl
    #
    tsmssub.h
    cA
    cB
    cB
    @0
    cH
    fco
    syl2anc
    tsmssub.x
    wph
    cA
    cB
    cH
    cG
    @0
    cV
    cY
    tsmssub.b
    @11
    tsmssub.1
    tsmssub.2
    tsmssub.a
    tsmssub.h
    tsmssub.y
    tsmsinv
    tsmsadd
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    @6
    @3
    wceq
    wph
    cG
    cF
    ctsu
    co
    cB
    cX
    wph
    cA
    cB
    cF
    cG
    cV
    tsmssub.b
    tsmssub.1
    wph
    @9
    cG
    ctps
    wcel
    tsmssub.2
    cG
    tgptps
    syl
    #
    tsmssub.a
    tsmssub.f
    tsmscl
    tsmssub.x
    sseldd
    wph
    cG
    cH
    ctsu
    co
    cB
    cY
    wph
    cA
    cB
    cH
    cG
    cV
    tsmssub.b
    tsmssub.1
    @13
    tsmssub.a
    tsmssub.h
    tsmscl
    tsmssub.y
    sseldd
    cB
    @2
    cG
    @0
    c.mi
    cX
    cY
    tsmssub.b
    @8
    @11
    tsmssub.p
    grpsubval
    syl2anc
    wph
    @7
    @5
    cG
    ctsu
    wph
    vk
    cA
    vk
    cv
    #
    cF
    cfv
    #
    @14
    cH
    cfv
    #
    c.mi
    co
    #
    cmpt
    vk
    cA
    @15
    @16
    @0
    cfv
    #
    @2
    co
    #
    cmpt
    @7
    @5
    wph
    vk
    cA
    @17
    @19
    wph
    @14
    cA
    wcel
    wa
    #
    @15
    cB
    wcel
    @16
    cB
    wcel
    @17
    @19
    wceq
    wph
    cA
    cB
    @14
    cF
    tsmssub.f
    ffvelrnda
    #
    wph
    cA
    cB
    @14
    cH
    tsmssub.h
    ffvelrnda
    #
    cB
    @2
    cG
    @0
    c.mi
    @15
    @16
    tsmssub.b
    @8
    @11
    tsmssub.p
    grpsubval
    syl2anc
    mpteq2dva
    wph
    vk
    cA
    @15
    @16
    c.mi
    cF
    cH
    cV
    cB
    cB
    tsmssub.a
    @21
    @22
    wph
    vk
    cA
    cB
    cF
    tsmssub.f
    feqmptd
    #
    wph
    vk
    cA
    cB
    cH
    tsmssub.h
    feqmptd
    #
    offval2
    wph
    vk
    cA
    @15
    @18
    @2
    cF
    @4
    cV
    cB
    cvv
    tsmssub.a
    @21
    @20
    @16
    @0
    fvexd
    @23
    wph
    vk
    vx
    cA
    cB
    @16
    vx
    cv
    #
    @0
    cfv
    @18
    cH
    @0
    @22
    @24
    wph
    vx
    cB
    cB
    @0
    @12
    feqmptd
    @25
    @16
    @0
    fveq2
    fmptco
    offval2
    3eqtr4d
    oveq2d
    3eltr4d
end
