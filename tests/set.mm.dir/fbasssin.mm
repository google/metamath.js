include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cpw.mm"
include "w3a.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "isfbas2.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "simp3d.mm"
include "wceq.mm"
include "ineq1.mm"
include "sseq2d.mm"
include "rexbidv.mm"
include "ineq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem fbasssin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint F y
  disjoint F z
  disjoint X y
  disjoint X z
  assert |- ( ( F e. ( fBas ` X ) /\ A e. F /\ B e. F ) -> E. x e. F x C_ ( A i^i B ) )

  proof
    cF
    cX
    cfbas
    cfv
    wcel
    #
    cA
    cF
    wcel
    #
    cB
    cF
    wcel
    #
    vx
    cv
    #
    cA
    cB
    cin
    #
    wss
    #
    vx
    cF
    wrex
    #
    @0
    @3
    vy
    cv
    #
    vz
    cv
    #
    cin
    #
    wss
    #
    vx
    cF
    wrex
    #
    vz
    cF
    wral
    vy
    cF
    wral
    #
    @1
    @2
    wa
    @6
    @0
    cF
    c0
    wne
    #
    c0
    cF
    wnel
    #
    @12
    @0
    cF
    cX
    cpw
    wss
    #
    @13
    @14
    @12
    w3a
    #
    @0
    @15
    @16
    wa
    #
    @0
    cX
    cfbas
    cdm
    #
    wcel
    @0
    @17
    wb
    cF
    cX
    cfbas
    elfvdm
    vy
    vz
    vx
    @18
    cX
    cF
    isfbas2
    syl
    ibi
    simprd
    simp3d
    @11
    @6
    @3
    cA
    @8
    cin
    #
    wss
    #
    vx
    cF
    wrex
    vy
    vz
    cA
    cB
    cF
    cF
    @7
    cA
    wceq
    #
    @10
    @20
    vx
    cF
    @21
    @9
    @19
    @3
    @7
    cA
    @8
    ineq1
    sseq2d
    rexbidv
    @8
    cB
    wceq
    #
    @20
    @5
    vx
    cF
    @22
    @19
    @4
    @3
    @8
    cB
    cA
    ineq2
    sseq2d
    rexbidv
    rspc2v
    syl5com
    3impib
end
