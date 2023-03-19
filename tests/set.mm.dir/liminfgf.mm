include "cr.mm"
include "cxr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cin.mm"
include "clt.mm"
include "cinf.mm"
include "wss.mm"
include "wcel.mm"
include "inss2.mm"
include "infxrcl.mm"
include "mp1i.mm"
include "fmpti.mm"

theorem liminfgf
  let vk: setvar k
  let cF: class F
  let cG: class G
  let vx: setvar x
  assume liminfgf.1: |- G = ( k e. RR |-> inf ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )


  assert |- G : RR --> RR*

  proof
    vk
    cr
    cxr
    cF
    vk
    cv
    #
    cpnf
    cico
    co
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    cinf
    #
    cG
    liminfgf.1
    @2
    cxr
    wss
    @3
    cxr
    wcel
    @0
    cr
    wcel
    @1
    cxr
    inss2
    @2
    infxrcl
    mp1i
    fmpti
end
