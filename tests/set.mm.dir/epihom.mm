include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "wa.mm"
include "isepi.mm"
include "simpl.mm"
include "syl6bi.mm"
include "ssrdv.mm"

theorem epihom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cE: class E
  let cH: class H
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vz: setvar z
  let vf: setvar f
  let vh: setvar h
  let cF: class F
  assume isepi.b: |- B = ( Base ` C )
  assume isepi.h: |- H = ( Hom ` C )
  assume isepi.o: |- .x. = ( comp ` C )
  assume isepi.e: |- E = ( Epi ` C )
  assume isepi.c: |- ( ph -> C e. Cat )
  assume isepi.x: |- ( ph -> X e. B )
  assume isepi.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X E Y ) C_ ( X H Y ) )

  proof
    wph
    vf
    cX
    cY
    cE
    co
    #
    cX
    cY
    cH
    co
    #
    wph
    vf
    cv
    #
    @0
    wcel
    @2
    @1
    wcel
    #
    vg
    cY
    vz
    cv
    #
    cH
    co
    vg
    cv
    @2
    cX
    cY
    cop
    @4
    c.x
    co
    co
    cmpt
    ccnv
    wfun
    vz
    cB
    wral
    #
    wa
    @3
    wph
    vz
    cB
    cC
    c.x
    vg
    cE
    @2
    cH
    cX
    cY
    isepi.b
    isepi.h
    isepi.o
    isepi.e
    isepi.c
    isepi.x
    isepi.y
    isepi
    @3
    @5
    simpl
    syl6bi
    ssrdv
end
