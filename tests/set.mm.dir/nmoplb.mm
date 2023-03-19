include "chil.mm"
include "wf.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cnop.mm"
include "wss.mm"
include "cr.mm"
include "nmopsetretHIL.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "3ad2ant1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "biantru.mm"
include "syl6bbr.mm"
include "rspcev.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "3adant1.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "nmopval.mm"
include "breqtrrd.mm"

theorem nmoplb
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T : ~H --> ~H /\ A e. ~H /\ ( normh ` A ) <_ 1 ) -> ( normh ` ( T ` A ) ) <_ ( normop ` T ) )

  proof
    chil
    chil
    cT
    wf
    #
    cA
    chil
    wcel
    #
    cA
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    w3a
    #
    cA
    cT
    cfv
    #
    cno
    cfv
    #
    vy
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @7
    cT
    cfv
    #
    cno
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cT
    cnop
    cfv
    #
    cle
    @4
    @16
    cxr
    wss
    #
    @6
    @16
    wcel
    #
    @6
    @17
    cle
    wbr
    @0
    @1
    @19
    @3
    @0
    @16
    cr
    cxr
    vx
    vy
    cT
    nmopsetretHIL
    ressxr
    syl6ss
    3ad2ant1
    @1
    @3
    @20
    @0
    @1
    @3
    wa
    @9
    @6
    @12
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    @20
    @22
    @3
    vy
    cA
    chil
    @7
    cA
    wceq
    #
    @22
    @3
    @6
    @6
    wceq
    #
    wa
    @3
    @24
    @9
    @3
    @21
    @25
    @24
    @8
    @2
    c1
    cle
    @7
    cA
    cno
    fveq2
    breq1d
    @24
    @12
    @6
    @6
    @24
    @11
    @5
    cno
    @7
    cA
    cT
    fveq2
    fveq2d
    eqeq2d
    anbi12d
    @25
    @3
    @6
    eqid
    biantru
    syl6bbr
    rspcev
    @15
    @23
    vx
    @6
    @5
    cno
    fvex
    @10
    @6
    wceq
    #
    @14
    @22
    vy
    chil
    @26
    @13
    @21
    @9
    @10
    @6
    @12
    eqeq1
    anbi2d
    rexbidv
    elab
    sylibr
    3adant1
    @16
    @6
    supxrub
    syl2anc
    @0
    @1
    @18
    @17
    wceq
    @3
    vx
    vy
    cT
    nmopval
    3ad2ant1
    breqtrrd
end
