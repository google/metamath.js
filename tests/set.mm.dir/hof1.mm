include "c1st.mm"
include "cfv.mm"
include "co.mm"
include "chomf.mm"
include "hof1fval.mm"
include "oveqd.mm"
include "eqid.mm"
include "homfval.mm"
include "eqtrd.mm"

theorem hof1
  let wph: wff ph
  let cB: class B
  let cC: class C
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
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let c.x: class .x.
  let cZ: class Z
  assume hofval.m: |- M = ( HomF ` C )
  assume hofval.c: |- ( ph -> C e. Cat )
  assume hof1.b: |- B = ( Base ` C )
  assume hof1.h: |- H = ( Hom ` C )
  assume hof1.x: |- ( ph -> X e. B )
  assume hof1.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X ( 1st ` M ) Y ) = ( X H Y ) )

  proof
    wph
    cX
    cY
    cM
    c1st
    cfv
    #
    co
    cX
    cY
    cC
    chomf
    cfv
    #
    co
    cX
    cY
    cH
    co
    wph
    @0
    @1
    cX
    cY
    wph
    cC
    cM
    hofval.m
    hofval.c
    hof1fval
    oveqd
    wph
    cB
    cC
    @1
    cH
    cX
    cY
    @1
    eqid
    hof1.b
    hof1.h
    hof1.x
    hof1.y
    homfval
    eqtrd
end
