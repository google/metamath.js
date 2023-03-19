include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "eltg.mm"
include "syl.mm"
include "ibi.mm"
include "inss2.mm"
include "unissi.mm"
include "unipw.mm"
include "sseqtri.mm"
include "a1i.mm"
include "eqssd.mm"

theorem eltg4i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cV: class V
  let cC: class C


  assert |- ( A e. ( topGen ` B ) -> A = U. ( B i^i ~P A ) )

  proof
    cA
    cB
    ctg
    cfv
    wcel
    #
    cA
    cB
    cA
    cpw
    #
    cin
    #
    cuni
    #
    @0
    cA
    @3
    wss
    #
    @0
    cB
    ctg
    cdm
    #
    wcel
    @0
    @4
    wb
    cA
    cB
    ctg
    elfvdm
    cA
    cB
    @5
    eltg
    syl
    ibi
    @3
    cA
    wss
    @0
    @3
    @1
    cuni
    cA
    @2
    @1
    cB
    @1
    inss2
    unissi
    cA
    unipw
    sseqtri
    a1i
    eqssd
end
