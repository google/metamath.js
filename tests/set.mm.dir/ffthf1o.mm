include "co.mm"
include "cfv.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "cful.mm"
include "wbr.mm"
include "cfth.mm"
include "cin.mm"
include "wa.mm"
include "brin.mm"
include "sylib.mm"
include "simprd.mm"
include "fthf1.mm"
include "simpld.mm"
include "fullfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem ffthf1o
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
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
  assume ffthf1o.f: |- ( ph -> F ( ( C Full D ) i^i ( C Faith D ) ) G )
  assume ffthf1o.x: |- ( ph -> X e. B )
  assume ffthf1o.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X G Y ) : ( X H Y ) -1-1-onto-> ( ( F ` X ) J ( F ` Y ) ) )

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
    @0
    @1
    @2
    wfo
    @0
    @1
    @2
    wf1o
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
    wph
    cF
    cG
    cC
    cD
    cful
    co
    #
    wbr
    #
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    #
    wph
    cF
    cG
    @3
    @5
    cin
    wbr
    @4
    @6
    wa
    ffthf1o.f
    cF
    cG
    @3
    @5
    brin
    sylib
    #
    simprd
    ffthf1o.x
    ffthf1o.y
    fthf1
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
    isfth.j
    isfth.h
    wph
    @4
    @6
    @7
    simpld
    ffthf1o.x
    ffthf1o.y
    fullfo
    @0
    @1
    @2
    df-f1o
    sylanbrc
end
