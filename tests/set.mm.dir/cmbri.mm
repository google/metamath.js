include "cch.mm"
include "wcel.mm"
include "ccm.mm"
include "wbr.mm"
include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "cmbr.mm"
include "mp2an.mm"

theorem cmbri
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B <-> A = ( ( A i^i B ) vH ( A i^i ( _|_ ` B ) ) ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    cA
    cB
    ccm
    wbr
    cA
    cA
    cB
    cin
    cA
    cB
    cort
    cfv
    cin
    chj
    co
    wceq
    wb
    pjoml2.1
    pjoml2.2
    cA
    cB
    cmbr
    mp2an
end
