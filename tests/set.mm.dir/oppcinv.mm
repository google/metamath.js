include "csect.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "cin.mm"
include "incom.mm"
include "eqid.mm"
include "oppcsect2.mm"
include "cnveqd.mm"
include "wrel.mm"
include "wceq.mm"
include "chom.mm"
include "cxp.mm"
include "wss.mm"
include "cco.mm"
include "ccid.mm"
include "sectss.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "dfrel2.mm"
include "sylib.mm"
include "eqtrd.mm"
include "ineq12d.mm"
include "syl5eq.mm"
include "oppcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "invfval.mm"
include "3eqtr4d.mm"

theorem oppcinv
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
  assume oppcinv.s: |- I = ( Inv ` C )
  assume oppcinv.t: |- J = ( Inv ` O )


  assert |- ( ph -> ( X J Y ) = ( Y I X ) )

  proof
    wph
    cX
    cY
    cO
    csect
    cfv
    #
    co
    #
    cY
    cX
    @0
    co
    #
    ccnv
    #
    cin
    #
    cY
    cX
    cC
    csect
    cfv
    #
    co
    #
    cX
    cY
    @5
    co
    ccnv
    #
    cin
    #
    cX
    cY
    cJ
    co
    cY
    cX
    cI
    co
    wph
    @4
    @3
    @1
    cin
    @8
    @1
    @3
    incom
    wph
    @3
    @6
    @1
    @7
    wph
    @3
    @6
    ccnv
    #
    ccnv
    #
    @6
    wph
    @2
    @9
    wph
    cB
    cC
    @5
    @0
    cO
    cY
    cX
    oppcsect.b
    oppcsect.o
    oppcsect.c
    oppcsect.y
    oppcsect.x
    @5
    eqid
    #
    @0
    eqid
    #
    oppcsect2
    cnveqd
    wph
    @6
    wrel
    #
    @10
    @6
    wceq
    wph
    @6
    cY
    cX
    cC
    chom
    cfv
    #
    co
    #
    cX
    cY
    @14
    co
    #
    cxp
    #
    wss
    @17
    wrel
    @13
    wph
    cB
    cC
    @5
    cC
    cco
    cfv
    #
    cC
    ccid
    cfv
    #
    @14
    cY
    cX
    oppcsect.b
    @14
    eqid
    @18
    eqid
    @19
    eqid
    @11
    oppcsect.c
    oppcsect.y
    oppcsect.x
    sectss
    @15
    @16
    relxp
    @6
    @17
    relss
    mpisyl
    @6
    dfrel2
    sylib
    eqtrd
    wph
    cB
    cC
    @5
    @0
    cO
    cX
    cY
    oppcsect.b
    oppcsect.o
    oppcsect.c
    oppcsect.x
    oppcsect.y
    @11
    @12
    oppcsect2
    ineq12d
    syl5eq
    wph
    cB
    cO
    @0
    cJ
    cX
    cY
    cB
    cC
    cO
    oppcsect.o
    oppcsect.b
    oppcbas
    oppcinv.t
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
    @12
    invfval
    wph
    cB
    cC
    @5
    cI
    cY
    cX
    oppcsect.b
    oppcinv.s
    oppcsect.c
    oppcsect.y
    oppcsect.x
    @11
    invfval
    3eqtr4d
end
