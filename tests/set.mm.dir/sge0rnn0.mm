include "cc0.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wrex.mm"
include "0elpw.mm"
include "0fin.mm"
include "elini.mm"
include "sum0.mm"
include "eqcomi.mm"
include "sumeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "ne0i.mm"

theorem sge0rnn0
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cX: class X
  let vk: setvar k

  disjoint F x
  disjoint X x
  disjoint x y
  disjoint k x
  assert |- ran ( x e. ( ~P X i^i Fin ) |-> sum_ y e. x ( F ` y ) ) =/= (/)

  proof
    cc0
    vx
    cX
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
    cF
    cfv
    #
    vy
    csu
    #
    cmpt
    #
    crn
    #
    wcel
    #
    @6
    c0
    wne
    @7
    cc0
    @4
    wceq
    #
    vx
    @1
    wrex
    #
    c0
    @1
    wcel
    cc0
    c0
    @3
    vy
    csu
    #
    wceq
    #
    @9
    c0
    @0
    cfn
    cX
    0elpw
    0fin
    elini
    @10
    cc0
    @3
    vy
    sum0
    eqcomi
    @8
    @11
    vx
    c0
    @1
    @2
    c0
    wceq
    @4
    @10
    cc0
    @2
    c0
    @3
    vy
    sumeq1
    eqeq2d
    rspcev
    mp2an
    cc0
    cr
    wcel
    @7
    @9
    wb
    0re
    vx
    @1
    @4
    cc0
    @5
    cr
    @5
    eqid
    elrnmpt
    ax-mp
    mpbir
    @6
    cc0
    ne0i
    ax-mp
end
