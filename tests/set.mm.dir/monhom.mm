include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "wa.mm"
include "ismon.mm"
include "simpl.mm"
include "syl6bi.mm"
include "ssrdv.mm"

theorem monhom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cH: class H
  let cM: class M
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cK: class K
  let cF: class F
  let cZ: class Z
  assume ismon.b: |- B = ( Base ` C )
  assume ismon.h: |- H = ( Hom ` C )
  assume ismon.o: |- .x. = ( comp ` C )
  assume ismon.s: |- M = ( Mono ` C )
  assume ismon.c: |- ( ph -> C e. Cat )
  assume ismon.x: |- ( ph -> X e. B )
  assume ismon.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X M Y ) C_ ( X H Y ) )

  proof
    wph
    vf
    cX
    cY
    cM
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
    vz
    cv
    #
    cX
    cH
    co
    @2
    vg
    cv
    @4
    cX
    cop
    cY
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
    @2
    cH
    cM
    cX
    cY
    ismon.b
    ismon.h
    ismon.o
    ismon.s
    ismon.c
    ismon.x
    ismon.y
    ismon
    @3
    @5
    simpl
    syl6bi
    ssrdv
end
