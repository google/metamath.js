include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "wi.mm"
include "wf1o.mm"
include "wf1.mm"
include "symgbasf1o.mm"
include "f1of1.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "adantl.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "f1veqaeq.mm"
include "syl12anc.mm"
include "adantr.mm"
include "sylbid.mm"
include "necon3d.mm"
include "3exp1.mm"
include "3syl.mm"
include "3imp.mm"

theorem symgfvne
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cV: class V
  assume symgbas.1: |- G = ( SymGrp ` A )
  assume symgbas.2: |- B = ( Base ` G )


  assert |- ( ( F e. B /\ X e. A /\ Y e. A ) -> ( ( F ` X ) = Z -> ( Y =/= X -> ( F ` Y ) =/= Z ) ) )

  proof
    cF
    cB
    wcel
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    cX
    cF
    cfv
    #
    cZ
    wceq
    #
    cY
    cX
    wne
    cY
    cF
    cfv
    #
    cZ
    wne
    wi
    #
    wi
    #
    @0
    cA
    cA
    cF
    wf1o
    cA
    cA
    cF
    wf1
    #
    @1
    @2
    @7
    wi
    wi
    cA
    cB
    cF
    cG
    symgbas.1
    symgbas.2
    symgbasf1o
    cA
    cA
    cF
    f1of1
    @8
    @1
    @2
    @4
    @6
    @8
    @1
    @2
    w3a
    #
    @4
    wa
    #
    @5
    cZ
    cY
    cX
    @10
    @5
    cZ
    wceq
    #
    @5
    @3
    wceq
    #
    cY
    cX
    wceq
    #
    @4
    @11
    @12
    wb
    #
    @9
    @14
    cZ
    @3
    cZ
    @3
    @5
    eqeq2
    eqcoms
    adantl
    @9
    @12
    @13
    wi
    #
    @4
    @9
    @8
    @2
    @1
    @15
    @8
    @1
    @2
    simp1
    @8
    @1
    @2
    simp3
    @8
    @1
    @2
    simp2
    cA
    cA
    cY
    cX
    cF
    f1veqaeq
    syl12anc
    adantr
    sylbid
    necon3d
    3exp1
    3syl
    3imp
end
