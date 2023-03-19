include "chil.mm"
include "wf.mm"
include "cc0.mm"
include "cnop.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wb.mm"
include "nmopxr.mm"
include "nmopge0.mm"
include "0xr.mm"
include "xrleltne.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "bicomd.mm"

theorem nmopgt0
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T : ~H --> ~H -> ( ( normop ` T ) =/= 0 <-> 0 < ( normop ` T ) ) )

  proof
    chil
    chil
    cT
    wf
    #
    cc0
    cT
    cnop
    cfv
    #
    clt
    wbr
    #
    @1
    cc0
    wne
    #
    @0
    @1
    cxr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @2
    @3
    wb
    #
    cT
    nmopxr
    cT
    nmopge0
    cc0
    cxr
    wcel
    @4
    @5
    @6
    0xr
    cc0
    @1
    xrleltne
    mp3an1
    syl2anc
    bicomd
end
