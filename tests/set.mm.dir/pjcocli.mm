include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "pjcoi.mm"
include "pjhcli.mm"
include "pjcli.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem pjcocli
  let cA: class A
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( A e. ~H -> ( ( ( projh ` G ) o. ( projh ` H ) ) ` A ) e. G )

  proof
    cA
    chil
    wcel
    #
    cA
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    cfv
    cA
    @2
    cfv
    #
    @1
    cfv
    #
    cG
    cA
    cG
    cH
    pjco.1
    pjco.2
    pjcoi
    @0
    @3
    chil
    wcel
    @4
    cG
    wcel
    cA
    cH
    pjco.2
    pjhcli
    @3
    cG
    pjco.1
    pjcli
    syl
    eqeltrd
end
