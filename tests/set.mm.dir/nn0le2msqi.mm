include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cc0.mm"
include "wb.mm"
include "nn0ge0i.mm"
include "nn0rei.mm"
include "le2sqi.mm"
include "mp2an.mm"
include "nn0cni.mm"
include "sqvali.mm"
include "breq12i.mm"
include "bitri.mm"

theorem nn0le2msqi
  let cA: class A
  let cB: class B
  assume nn0le2msqi.1: |- A e. NN0
  assume nn0le2msqi.2: |- B e. NN0


  assert |- ( A <_ B <-> ( A x. A ) <_ ( B x. B ) )

  proof
    cA
    cB
    cle
    wbr
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cle
    wbr
    #
    cA
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    cle
    wbr
    cc0
    cA
    cle
    wbr
    cc0
    cB
    cle
    wbr
    @0
    @3
    wb
    cA
    nn0le2msqi.1
    nn0ge0i
    cB
    nn0le2msqi.2
    nn0ge0i
    cA
    cB
    cA
    nn0le2msqi.1
    nn0rei
    cB
    nn0le2msqi.2
    nn0rei
    le2sqi
    mp2an
    @1
    @4
    @2
    @5
    cle
    cA
    cA
    nn0le2msqi.1
    nn0cni
    sqvali
    cB
    cB
    nn0le2msqi.2
    nn0cni
    sqvali
    breq12i
    bitri
end
