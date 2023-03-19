include "co.mm"
include "wbr.mm"
include "cop.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "homaval.mm"
include "breqd.mm"
include "brxp.mm"
include "opex.mm"
include "elsn2.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem elhoma
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vx: setvar x
  let vz: setvar z
  assume homarcl.h: |- H = ( HomA ` C )
  assume homafval.b: |- B = ( Base ` C )
  assume homafval.c: |- ( ph -> C e. Cat )
  assume homaval.j: |- J = ( Hom ` C )
  assume homaval.x: |- ( ph -> X e. B )
  assume homaval.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( Z ( X H Y ) F <-> ( Z = <. X , Y >. /\ F e. ( X J Y ) ) ) )

  proof
    wph
    cZ
    cF
    cX
    cY
    cH
    co
    #
    wbr
    cZ
    cF
    cX
    cY
    cop
    #
    csn
    #
    cX
    cY
    cJ
    co
    #
    cxp
    #
    wbr
    #
    cZ
    @1
    wceq
    #
    cF
    @3
    wcel
    #
    wa
    #
    wph
    @0
    @4
    cZ
    cF
    wph
    cB
    cC
    cH
    cJ
    cX
    cY
    homarcl.h
    homafval.b
    homafval.c
    homaval.j
    homaval.x
    homaval.y
    homaval
    breqd
    @5
    cZ
    @2
    wcel
    #
    @7
    wa
    @8
    cZ
    cF
    @2
    @3
    brxp
    @9
    @6
    @7
    cZ
    @1
    cX
    cY
    opex
    elsn2
    anbi1i
    bitri
    syl6bb
end
