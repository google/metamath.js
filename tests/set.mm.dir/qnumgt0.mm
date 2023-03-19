include "cq.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdenom.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cnumer.mm"
include "cr.mm"
include "wb.mm"
include "0red.mm"
include "qre.mm"
include "qdencl.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "nncnd.mm"
include "mul02d.mm"
include "qmuldeneqnum.mm"
include "breq12d.mm"
include "bitrd.mm"

theorem qnumgt0
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. QQ -> ( 0 < A <-> 0 < ( numer ` A ) ) )

  proof
    cA
    cq
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    cdenom
    cfv
    #
    cmul
    co
    #
    cA
    @2
    cmul
    co
    #
    clt
    wbr
    #
    cc0
    cA
    cnumer
    cfv
    #
    clt
    wbr
    @0
    cc0
    cr
    wcel
    cA
    cr
    wcel
    @2
    cr
    wcel
    cc0
    @2
    clt
    wbr
    @1
    @5
    wb
    @0
    0red
    cA
    qre
    @0
    @2
    cA
    qdencl
    #
    nnred
    @0
    @2
    @7
    nngt0d
    cc0
    cA
    @2
    ltmul1
    syl112anc
    @0
    @3
    cc0
    @4
    @6
    clt
    @0
    @2
    @0
    @2
    @7
    nncnd
    mul02d
    cA
    qmuldeneqnum
    breq12d
    bitrd
end
