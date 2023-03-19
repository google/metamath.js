include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crio.mm"
include "idrval.mm"
include "wreu.mm"
include "exidu1.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem iorlid
  let cU: class U
  let cG: class G
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  assume iorlid.1: |- X = ran G
  assume iorlid.2: |- U = ( GId ` G )


  assert |- ( G e. ( Magma i^i ExId ) -> U e. X )

  proof
    cG
    cmagm
    cexid
    cin
    #
    wcel
    #
    cU
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    @3
    wceq
    @3
    @2
    cG
    co
    @3
    wceq
    wa
    vx
    cX
    wral
    #
    vu
    cX
    crio
    #
    cX
    vx
    vu
    @0
    cU
    cG
    cX
    iorlid.1
    iorlid.2
    idrval
    @1
    @4
    vu
    cX
    wreu
    @5
    cX
    wcel
    vx
    vu
    cG
    cX
    iorlid.1
    exidu1
    @4
    vu
    cX
    riotacl
    syl
    eqeltrd
end
