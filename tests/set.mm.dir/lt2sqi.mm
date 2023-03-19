include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "lt2msqi.mm"
include "recni.mm"
include "sqvali.mm"
include "breq12i.mm"
include "syl6bbr.mm"

theorem lt2sqi
  let cA: class A
  let cB: class B
  assume resqcl.1: |- A e. RR
  assume lt2sq.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> ( A < B <-> ( A ^ 2 ) < ( B ^ 2 ) ) )

  proof
    cc0
    cA
    cle
    wbr
    cc0
    cB
    cle
    wbr
    wa
    cA
    cB
    clt
    wbr
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
    clt
    wbr
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
    clt
    wbr
    cA
    cB
    resqcl.1
    lt2sq.2
    lt2msqi
    @2
    @0
    @3
    @1
    clt
    cA
    cA
    resqcl.1
    recni
    sqvali
    cB
    cB
    lt2sq.2
    recni
    sqvali
    breq12i
    syl6bbr
end
