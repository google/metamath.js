include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "jca.mm"
include "w3a.mm"
include "issect.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "baibd.mm"
include "mpdan.mm"

theorem issect2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume issect.b: |- B = ( Base ` C )
  assume issect.h: |- H = ( Hom ` C )
  assume issect.o: |- .x. = ( comp ` C )
  assume issect.i: |- .1. = ( Id ` C )
  assume issect.s: |- S = ( Sect ` C )
  assume issect.c: |- ( ph -> C e. Cat )
  assume issect.x: |- ( ph -> X e. B )
  assume issect.y: |- ( ph -> Y e. B )
  assume issect.f: |- ( ph -> F e. ( X H Y ) )
  assume issect.g: |- ( ph -> G e. ( Y H X ) )


  assert |- ( ph -> ( F ( X S Y ) G <-> ( G ( <. X , Y >. .x. X ) F ) = ( .1. ` X ) ) )

  proof
    wph
    cF
    cX
    cY
    cH
    co
    wcel
    #
    cG
    cY
    cX
    cH
    co
    wcel
    #
    wa
    #
    cF
    cG
    cX
    cY
    cS
    co
    wbr
    #
    cG
    cF
    cX
    cY
    cop
    cX
    c.x
    co
    co
    cX
    c.1
    cfv
    wceq
    #
    wb
    wph
    @0
    @1
    issect.f
    issect.g
    jca
    wph
    @3
    @2
    @4
    wph
    @3
    @0
    @1
    @4
    w3a
    @2
    @4
    wa
    wph
    cB
    cC
    cS
    c.x
    c.1
    cF
    cG
    cH
    cX
    cY
    issect.b
    issect.h
    issect.o
    issect.i
    issect.s
    issect.c
    issect.x
    issect.y
    issect
    @0
    @1
    @4
    df-3an
    syl6bb
    baibd
    mpdan
end
