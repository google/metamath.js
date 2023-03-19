include "cminusg.mm"
include "cfv.mm"
include "ccom.mm"
include "cplusg.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "eqid.mm"
include "cabl.mm"
include "wcel.mm"
include "ccmn.mm"
include "ablcmn.mm"
include "syl.mm"
include "wf.mm"
include "wf1o.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "grpinvf1o.mm"
include "f1of.mm"
include "fco.mm"
include "syl2anc.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cbs.mm"
include "wceq.mm"
include "grpinvid.mm"
include "fsuppco2.mm"
include "gsumadd.mm"
include "gsuminv.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "cv.mm"
include "cmpt.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "grpsubval.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "offval2.mm"
include "fvexd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "gsumcl.mm"

theorem gsumsub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cV: class V
  let c.0: class .0.
  let vk: setvar k
  let vx: setvar x
  assume gsumsub.b: |- B = ( Base ` G )
  assume gsumsub.z: |- .0. = ( 0g ` G )
  assume gsumsub.m: |- .- = ( -g ` G )
  assume gsumsub.g: |- ( ph -> G e. Abel )
  assume gsumsub.a: |- ( ph -> A e. V )
  assume gsumsub.f: |- ( ph -> F : A --> B )
  assume gsumsub.h: |- ( ph -> H : A --> B )
  assume gsumsub.fn: |- ( ph -> F finSupp .0. )
  assume gsumsub.hn: |- ( ph -> H finSupp .0. )


  assert |- ( ph -> ( G gsum ( F oF .- H ) ) = ( ( G gsum F ) .- ( G gsum H ) ) )

  proof
    wph
    cG
    cF
    cG
    cminusg
    cfv
    #
    cH
    ccom
    #
    cG
    cplusg
    cfv
    #
    cof
    co
    #
    cgsu
    co
    #
    cG
    cF
    cgsu
    co
    #
    cG
    cH
    cgsu
    co
    #
    @0
    cfv
    #
    @2
    co
    #
    cG
    cF
    cH
    c.mi
    cof
    co
    #
    cgsu
    co
    @5
    @6
    c.mi
    co
    #
    wph
    @4
    @5
    cG
    @1
    cgsu
    co
    #
    @2
    co
    @8
    wph
    cA
    cB
    @2
    cF
    cG
    @1
    cV
    c.0
    gsumsub.b
    gsumsub.z
    @2
    eqid
    #
    wph
    cG
    cabl
    wcel
    #
    cG
    ccmn
    wcel
    gsumsub.g
    cG
    ablcmn
    syl
    #
    gsumsub.a
    gsumsub.f
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
    @1
    wf
    wph
    cB
    cB
    @0
    wf1o
    @15
    wph
    cB
    cG
    @0
    gsumsub.b
    @0
    eqid
    #
    wph
    @13
    cG
    cgrp
    wcel
    #
    gsumsub.g
    cG
    ablgrp
    syl
    #
    grpinvf1o
    cB
    cB
    @0
    f1of
    syl
    #
    gsumsub.h
    cA
    cB
    cB
    @0
    cH
    fco
    syl2anc
    gsumsub.fn
    wph
    cA
    cB
    cV
    cH
    @0
    cvv
    cvv
    c.0
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsumsub.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    gsumsub.h
    @19
    gsumsub.a
    cB
    cvv
    wcel
    wph
    cB
    cG
    cbs
    cfv
    cvv
    gsumsub.b
    cG
    cbs
    fvex
    eqeltri
    a1i
    gsumsub.hn
    wph
    @17
    c.0
    @0
    cfv
    c.0
    wceq
    @18
    cG
    @0
    c.0
    gsumsub.z
    @16
    grpinvid
    syl
    fsuppco2
    gsumadd
    wph
    @11
    @7
    @5
    @2
    wph
    cA
    cB
    cH
    cG
    @0
    cV
    c.0
    gsumsub.b
    gsumsub.z
    @16
    gsumsub.g
    gsumsub.a
    gsumsub.h
    gsumsub.hn
    gsuminv
    oveq2d
    eqtrd
    wph
    @9
    @3
    cG
    cgsu
    wph
    vk
    cA
    vk
    cv
    #
    cF
    cfv
    #
    @20
    cH
    cfv
    #
    c.mi
    co
    #
    cmpt
    vk
    cA
    @21
    @22
    @0
    cfv
    #
    @2
    co
    #
    cmpt
    @9
    @3
    wph
    vk
    cA
    @23
    @25
    wph
    @20
    cA
    wcel
    wa
    #
    @21
    cB
    wcel
    @22
    cB
    wcel
    @23
    @25
    wceq
    wph
    cA
    cB
    @20
    cF
    gsumsub.f
    ffvelrnda
    #
    wph
    cA
    cB
    @20
    cH
    gsumsub.h
    ffvelrnda
    #
    cB
    @2
    cG
    @0
    c.mi
    @21
    @22
    gsumsub.b
    @12
    @16
    gsumsub.m
    grpsubval
    syl2anc
    mpteq2dva
    wph
    vk
    cA
    @21
    @22
    c.mi
    cF
    cH
    cV
    cB
    cB
    gsumsub.a
    @27
    @28
    wph
    vk
    cA
    cB
    cF
    gsumsub.f
    feqmptd
    #
    wph
    vk
    cA
    cB
    cH
    gsumsub.h
    feqmptd
    #
    offval2
    wph
    vk
    cA
    @21
    @24
    @2
    cF
    @1
    cV
    cB
    cvv
    gsumsub.a
    @27
    @26
    @22
    @0
    fvexd
    @29
    wph
    vk
    vx
    cA
    cB
    @22
    vx
    cv
    #
    @0
    cfv
    @24
    cH
    @0
    @28
    @30
    wph
    vx
    cB
    cB
    @0
    @19
    feqmptd
    @31
    @22
    @0
    fveq2
    fmptco
    offval2
    3eqtr4d
    oveq2d
    wph
    @5
    cB
    wcel
    @6
    cB
    wcel
    @10
    @8
    wceq
    wph
    cA
    cB
    cF
    cG
    cV
    c.0
    gsumsub.b
    gsumsub.z
    @14
    gsumsub.a
    gsumsub.f
    gsumsub.fn
    gsumcl
    wph
    cA
    cB
    cH
    cG
    cV
    c.0
    gsumsub.b
    gsumsub.z
    @14
    gsumsub.a
    gsumsub.h
    gsumsub.hn
    gsumcl
    cB
    @2
    cG
    @0
    c.mi
    @5
    @6
    gsumsub.b
    @12
    @16
    gsumsub.m
    grpsubval
    syl2anc
    3eqtr4d
end
