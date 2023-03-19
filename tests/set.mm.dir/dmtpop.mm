include "cop.mm"
include "ctp.mm"
include "cdm.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "dmeqi.mm"
include "dmun.mm"
include "dmprop.mm"
include "dmsnop.mm"
include "uneq12i.mm"
include "3eqtri.mm"
include "eqtr4i.mm"

theorem dmtpop
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume dmsnop.1: |- B e. _V
  assume dmprop.1: |- D e. _V
  assume dmtpop.1: |- F e. _V


  assert |- dom { <. A , B >. , <. C , D >. , <. E , F >. } = { A , C , E }

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cE
    cF
    cop
    #
    ctp
    #
    cdm
    #
    cA
    cC
    cpr
    #
    cE
    csn
    #
    cun
    #
    cA
    cC
    cE
    ctp
    @4
    @0
    @1
    cpr
    #
    @2
    csn
    #
    cun
    #
    cdm
    @8
    cdm
    #
    @9
    cdm
    #
    cun
    @7
    @3
    @10
    @0
    @1
    @2
    df-tp
    dmeqi
    @8
    @9
    dmun
    @11
    @5
    @12
    @6
    cA
    cB
    cC
    cD
    dmsnop.1
    dmprop.1
    dmprop
    cE
    cF
    dmtpop.1
    dmsnop
    uneq12i
    3eqtri
    cA
    cC
    cE
    df-tp
    eqtr4i
end
