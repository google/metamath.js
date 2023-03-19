include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cpjh.mm"
include "cort.mm"
include "cva.mm"
include "caddc.mm"
include "pjpji.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "csh.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "chshii.mm"
include "shococss.mm"
include "choccli.mm"
include "pjopythi.mm"
include "mp2b.mm"
include "eqtri.mm"

theorem pjpythi
  let cA: class A
  let cH: class H
  assume pjnorm.1: |- H e. CH
  assume pjnorm.2: |- A e. ~H


  assert |- ( ( normh ` A ) ^ 2 ) = ( ( ( normh ` ( ( projh ` H ) ` A ) ) ^ 2 ) + ( ( normh ` ( ( projh ` ( _|_ ` H ) ) ` A ) ) ^ 2 ) )

  proof
    cA
    cno
    cfv
    #
    c2
    cexp
    co
    cA
    cH
    cpjh
    cfv
    cfv
    #
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
    c2
    cexp
    co
    #
    @1
    cno
    cfv
    c2
    cexp
    co
    @3
    cno
    cfv
    c2
    cexp
    co
    caddc
    co
    #
    @0
    @5
    c2
    cexp
    cA
    @4
    cno
    cA
    cH
    pjnorm.1
    pjnorm.2
    pjpji
    fveq2i
    oveq1i
    cH
    csh
    wcel
    cH
    @2
    cort
    cfv
    wss
    @6
    @7
    wceq
    cH
    pjnorm.1
    chshii
    cH
    shococss
    cA
    cH
    @2
    pjnorm.1
    cH
    pjnorm.1
    choccli
    pjnorm.2
    pjopythi
    mp2b
    eqtri
end
