include "wf.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "wral.mm"
include "wa.mm"
include "wreu.mm"
include "dff3.mm"
include "wcel.mm"
include "cop.mm"
include "df-br.mm"
include "ssel.mm"
include "opelxp2.mm"
include "syl6.mm"
include "syl5bi.mm"
include "pm4.71rd.mm"
include "eubidv.mm"
include "df-reu.mm"
include "syl6bbr.mm"
include "ralbidv.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem dff4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B z
  disjoint F z
  assert |- ( F : A --> B <-> ( F C_ ( A X. B ) /\ A. x e. A E! y e. B x F y ) )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    cB
    cxp
    #
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vy
    weu
    #
    vx
    cA
    wral
    #
    wa
    @1
    @4
    vy
    cB
    wreu
    #
    vx
    cA
    wral
    #
    wa
    vx
    vy
    cA
    cB
    cF
    dff3
    @1
    @6
    @8
    @1
    @5
    @7
    vx
    cA
    @1
    @5
    @3
    cB
    wcel
    #
    @4
    wa
    #
    vy
    weu
    @7
    @1
    @4
    @10
    vy
    @1
    @4
    @9
    @4
    @2
    @3
    cop
    #
    cF
    wcel
    #
    @1
    @9
    @2
    @3
    cF
    df-br
    @1
    @12
    @11
    @0
    wcel
    @9
    cF
    @0
    @11
    ssel
    @2
    @3
    cA
    cB
    opelxp2
    syl6
    syl5bi
    pm4.71rd
    eubidv
    @4
    vy
    cB
    df-reu
    syl6bbr
    ralbidv
    pm5.32i
    bitri
end
