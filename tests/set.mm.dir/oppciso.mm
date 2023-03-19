include "cinv.mm"
include "cfv.mm"
include "co.mm"
include "cdm.mm"
include "eqid.mm"
include "oppcinv.mm"
include "dmeqd.mm"
include "oppcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "isoval.mm"
include "3eqtr4d.mm"

theorem oppciso
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cJ: class J
  let cO: class O
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let cS: class S
  let cT: class T
  assume oppcsect.b: |- B = ( Base ` C )
  assume oppcsect.o: |- O = ( oppCat ` C )
  assume oppcsect.c: |- ( ph -> C e. Cat )
  assume oppcsect.x: |- ( ph -> X e. B )
  assume oppcsect.y: |- ( ph -> Y e. B )
  assume oppciso.s: |- I = ( Iso ` C )
  assume oppciso.t: |- J = ( Iso ` O )


  assert |- ( ph -> ( X J Y ) = ( Y I X ) )

  proof
    wph
    cX
    cY
    cO
    cinv
    cfv
    #
    co
    #
    cdm
    cY
    cX
    cC
    cinv
    cfv
    #
    co
    #
    cdm
    cX
    cY
    cJ
    co
    cY
    cX
    cI
    co
    wph
    @1
    @3
    wph
    cB
    cC
    @2
    @0
    cO
    cX
    cY
    oppcsect.b
    oppcsect.o
    oppcsect.c
    oppcsect.x
    oppcsect.y
    @2
    eqid
    #
    @0
    eqid
    #
    oppcinv
    dmeqd
    wph
    cB
    cO
    cJ
    @0
    cX
    cY
    cB
    cC
    cO
    oppcsect.o
    oppcsect.b
    oppcbas
    @5
    wph
    cC
    ccat
    wcel
    cO
    ccat
    wcel
    oppcsect.c
    cC
    cO
    oppcsect.o
    oppccat
    syl
    oppcsect.x
    oppcsect.y
    oppciso.t
    isoval
    wph
    cB
    cC
    cI
    @2
    cY
    cX
    oppcsect.b
    @4
    oppcsect.c
    oppcsect.y
    oppcsect.x
    oppciso.s
    isoval
    3eqtr4d
end
