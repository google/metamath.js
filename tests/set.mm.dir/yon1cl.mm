include "cfunc.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "cfuc.mm"
include "c2nd.mm"
include "eqid.mm"
include "fucbas.mm"
include "wrel.mm"
include "wcel.mm"
include "wbr.mm"
include "relfunc.mm"
include "yoncl.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "ffvelrnd.mm"

theorem yon1cl
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cO: class O
  let cV: class V
  let cX: class X
  let cY: class Y
  assume yon11.y: |- Y = ( Yon ` C )
  assume yon11.b: |- B = ( Base ` C )
  assume yon11.c: |- ( ph -> C e. Cat )
  assume yon11.p: |- ( ph -> X e. B )
  assume yon1cl.o: |- O = ( oppCat ` C )
  assume yon1cl.s: |- S = ( SetCat ` U )
  assume yon1cl.u: |- ( ph -> U e. V )
  assume yon1cl.h: |- ( ph -> ran ( Homf ` C ) C_ U )


  assert |- ( ph -> ( ( 1st ` Y ) ` X ) e. ( O Func S ) )

  proof
    wph
    cB
    cO
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
    cC
    cO
    cS
    cfuc
    co
    #
    @1
    cY
    c2nd
    cfv
    #
    yon11.b
    cO
    cS
    @2
    @2
    eqid
    #
    fucbas
    wph
    cC
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
    cC
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
    yon11.y
    yon11.c
    yon1cl.o
    yon1cl.s
    @4
    yon1cl.u
    yon1cl.h
    yoncl
    cY
    @5
    1st2ndbr
    sylancr
    funcf1
    yon11.p
    ffvelrnd
end
