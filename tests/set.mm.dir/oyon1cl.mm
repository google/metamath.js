include "cfunc.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "cfuc.mm"
include "c2nd.mm"
include "oppcbas.mm"
include "eqid.mm"
include "fucbas.mm"
include "wrel.mm"
include "wcel.mm"
include "wbr.mm"
include "relfunc.mm"
include "oyoncl.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "ffvelrnd.mm"

theorem oyon1cl
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cO: class O
  let cV: class V
  let cX: class X
  let cY: class Y
  assume oyoncl.o: |- O = ( oppCat ` C )
  assume oyoncl.y: |- Y = ( Yon ` O )
  assume oyoncl.c: |- ( ph -> C e. Cat )
  assume oyoncl.s: |- S = ( SetCat ` U )
  assume oyoncl.u: |- ( ph -> U e. V )
  assume oyoncl.h: |- ( ph -> ran ( Homf ` C ) C_ U )
  assume oyon1cl.b: |- B = ( Base ` C )
  assume oyon1cl.p: |- ( ph -> X e. B )


  assert |- ( ph -> ( ( 1st ` Y ) ` X ) e. ( C Func S ) )

  proof
    wph
    cB
    cC
    cS
    cfunc
    co
    #
    cX
    cY
    c1st
    cfv
    #
    wph
    cB
    @0
    cO
    cC
    cS
    cfuc
    co
    #
    @1
    cY
    c2nd
    cfv
    #
    cB
    cC
    cO
    oyoncl.o
    oyon1cl.b
    oppcbas
    cC
    cS
    @2
    @2
    eqid
    #
    fucbas
    wph
    cO
    @2
    cfunc
    co
    #
    wrel
    cY
    @5
    wcel
    @1
    @3
    @5
    wbr
    cO
    @2
    relfunc
    wph
    cC
    @2
    cS
    cU
    cO
    cV
    cY
    oyoncl.o
    oyoncl.y
    oyoncl.c
    oyoncl.s
    oyoncl.u
    oyoncl.h
    @4
    oyoncl
    cY
    @5
    1st2ndbr
    sylancr
    funcf1
    oyon1cl.p
    ffvelrnd
end
