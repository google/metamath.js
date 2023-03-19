include "co.mm"
include "ccnv.mm"
include "chom.mm"
include "cfv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "cco.mm"
include "ccid.mm"
include "oppcbas.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "sectss.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "relcnv.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "oppcsect.mm"
include "vex.mm"
include "brcnv.mm"
include "syl6bbr.mm"
include "eqbrrdv.mm"

theorem oppcsect2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cO: class O
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  assume oppcsect.b: |- B = ( Base ` C )
  assume oppcsect.o: |- O = ( oppCat ` C )
  assume oppcsect.c: |- ( ph -> C e. Cat )
  assume oppcsect.x: |- ( ph -> X e. B )
  assume oppcsect.y: |- ( ph -> Y e. B )
  assume oppcsect.s: |- S = ( Sect ` C )
  assume oppcsect.t: |- T = ( Sect ` O )


  assert |- ( ph -> ( X T Y ) = `' ( X S Y ) )

  proof
    wph
    vf
    vg
    cX
    cY
    cT
    co
    #
    cX
    cY
    cS
    co
    #
    ccnv
    #
    wph
    @0
    cX
    cY
    cO
    chom
    cfv
    #
    co
    #
    cY
    cX
    @3
    co
    #
    cxp
    #
    wss
    @6
    wrel
    @0
    wrel
    wph
    cB
    cO
    cT
    cO
    cco
    cfv
    #
    cO
    ccid
    cfv
    #
    @3
    cX
    cY
    cB
    cC
    cO
    oppcsect.o
    oppcsect.b
    oppcbas
    @3
    eqid
    @7
    eqid
    @8
    eqid
    oppcsect.t
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
    sectss
    @4
    @5
    relxp
    @0
    @6
    relss
    mpisyl
    @2
    wrel
    wph
    @1
    relcnv
    a1i
    wph
    vf
    cv
    #
    vg
    cv
    #
    @0
    wbr
    @10
    @9
    @1
    wbr
    @9
    @10
    @2
    wbr
    wph
    cB
    cC
    cS
    cT
    @9
    @10
    cO
    cX
    cY
    oppcsect.b
    oppcsect.o
    oppcsect.c
    oppcsect.x
    oppcsect.y
    oppcsect.s
    oppcsect.t
    oppcsect
    @9
    @10
    @1
    vf
    vex
    vg
    vex
    brcnv
    syl6bbr
    eqbrrdv
end
