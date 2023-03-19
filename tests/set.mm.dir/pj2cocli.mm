include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "pjfi.mm"
include "ho2coi.mm"
include "pjhcli.mm"
include "pjcli.mm"
include "3syl.mm"
include "eqeltrd.mm"

theorem pj2cocli
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjadj2co.1: |- F e. CH
  assume pjadj2co.2: |- G e. CH
  assume pjadj2co.3: |- H e. CH


  assert |- ( A e. ~H -> ( ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) ` A ) e. F )

  proof
    cA
    chil
    wcel
    #
    cA
    cF
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    ccom
    cH
    cpjh
    cfv
    #
    ccom
    cfv
    cA
    @3
    cfv
    #
    @2
    cfv
    #
    @1
    cfv
    #
    cF
    cA
    @1
    @2
    @3
    cF
    pjadj2co.1
    pjfi
    cG
    pjadj2co.2
    pjfi
    cH
    pjadj2co.3
    pjfi
    ho2coi
    @0
    @4
    chil
    wcel
    @5
    chil
    wcel
    @6
    cF
    wcel
    cA
    cH
    pjadj2co.3
    pjhcli
    @4
    cG
    pjadj2co.2
    pjhcli
    @5
    cF
    pjadj2co.1
    pjcli
    3syl
    eqeltrd
end
