include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "cort.mm"
include "cva.mm"
include "co.mm"
include "cle.mm"
include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "csp.mm"
include "cc0.mm"
include "wceq.mm"
include "wbr.mm"
include "pjhclii.mm"
include "choccli.mm"
include "pm3.2i.mm"
include "cch.mm"
include "pjorthi.mm"
include "ax-mp.mm"
include "normpyc.mm"
include "mp2.mm"
include "pjpji.mm"
include "fveq2i.mm"
include "breqtrri.mm"

theorem pjnormi
  let cA: class A
  let cH: class H
  assume pjnorm.1: |- H e. CH
  assume pjnorm.2: |- A e. ~H


  assert |- ( normh ` ( ( projh ` H ) ` A ) ) <_ ( normh ` A )

  proof
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    @0
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    cva
    co
    #
    cno
    cfv
    #
    cA
    cno
    cfv
    cle
    @0
    chil
    wcel
    #
    @3
    chil
    wcel
    #
    wa
    @0
    @3
    csp
    co
    cc0
    wceq
    #
    @1
    @5
    cle
    wbr
    @6
    @7
    cA
    cH
    pjnorm.1
    pjnorm.2
    pjhclii
    cA
    @2
    cH
    pjnorm.1
    choccli
    pjnorm.2
    pjhclii
    pm3.2i
    cH
    cch
    wcel
    @8
    pjnorm.1
    cA
    cA
    cH
    pjnorm.2
    pjnorm.2
    pjorthi
    ax-mp
    @0
    @3
    normpyc
    mp2
    cA
    @4
    cno
    cA
    cH
    pjnorm.1
    pjnorm.2
    pjpji
    fveq2i
    breqtrri
end
