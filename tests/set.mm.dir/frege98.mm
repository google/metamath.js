include "ctcl.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "whe.mm"
include "frege97.mm"
include "cvv.mm"
include "fvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "frege84.mm"
include "cop.mm"
include "elexi.mm"
include "elimasn.mm"
include "df-br.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "3imtr3i.mm"

theorem frege98
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume frege98.x: |- X e. A
  assume frege98.y: |- Y e. B
  assume frege98.z: |- Z e. C
  assume frege98.r: |- R e. D


  assert |- ( X ( t+ ` R ) Y -> ( Y ( t+ ` R ) Z -> X ( t+ ` R ) Z ) )

  proof
    cY
    cR
    ctcl
    cfv
    #
    cX
    csn
    #
    cima
    #
    wcel
    #
    cY
    cZ
    @0
    wbr
    #
    cZ
    @2
    wcel
    #
    wi
    #
    cX
    cY
    @0
    wbr
    #
    @4
    cX
    cZ
    @0
    wbr
    #
    wi
    @2
    cR
    whe
    @3
    @6
    wi
    cR
    cA
    cD
    cX
    frege98.x
    frege98.r
    frege97
    @2
    cvv
    cR
    cB
    cC
    cD
    cY
    cZ
    frege98.y
    frege98.z
    frege98.r
    @0
    cvv
    wcel
    @2
    cvv
    wcel
    cR
    ctcl
    fvex
    @0
    @1
    cvv
    imaexg
    ax-mp
    frege84
    ax-mp
    @3
    cX
    cY
    cop
    @0
    wcel
    @7
    @0
    cX
    cY
    cX
    cA
    frege98.x
    elexi
    #
    cY
    cB
    frege98.y
    elexi
    elimasn
    cX
    cY
    @0
    df-br
    bitr4i
    @5
    @8
    @4
    @5
    cX
    cZ
    cop
    @0
    wcel
    @8
    @0
    cX
    cZ
    @9
    cZ
    cC
    frege98.z
    elexi
    elimasn
    cX
    cZ
    @0
    df-br
    bitr4i
    imbi2i
    3imtr3i
end
