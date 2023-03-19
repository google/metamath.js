include "co.mm"
include "cfv.mm"
include "wf1.mm"
include "wcel.mm"
include "wceq.mm"
include "wb.mm"
include "fthf1.mm"
include "f1fveq.mm"
include "syl12anc.mm"

theorem fthi
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume isfth.b: |- B = ( Base ` C )
  assume isfth.h: |- H = ( Hom ` C )
  assume isfth.j: |- J = ( Hom ` D )
  assume fthf1.f: |- ( ph -> F ( C Faith D ) G )
  assume fthf1.x: |- ( ph -> X e. B )
  assume fthf1.y: |- ( ph -> Y e. B )
  assume fthi.r: |- ( ph -> R e. ( X H Y ) )
  assume fthi.s: |- ( ph -> S e. ( X H Y ) )


  assert |- ( ph -> ( ( ( X G Y ) ` R ) = ( ( X G Y ) ` S ) <-> R = S ) )

  proof
    wph
    cX
    cY
    cH
    co
    #
    cX
    cF
    cfv
    cY
    cF
    cfv
    cJ
    co
    #
    cX
    cY
    cG
    co
    #
    wf1
    cR
    @0
    wcel
    cS
    @0
    wcel
    cR
    @2
    cfv
    cS
    @2
    cfv
    wceq
    cR
    cS
    wceq
    wb
    wph
    cB
    cC
    cD
    cF
    cG
    cH
    cJ
    cX
    cY
    isfth.b
    isfth.h
    isfth.j
    fthf1.f
    fthf1.x
    fthf1.y
    fthf1
    fthi.r
    fthi.s
    @0
    @1
    cR
    cS
    @2
    f1fveq
    syl12anc
end
