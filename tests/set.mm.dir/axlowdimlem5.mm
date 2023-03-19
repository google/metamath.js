include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cop.mm"
include "cpr.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "cee.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "axlowdimlem4.mm"
include "axlowdimlem1.mm"
include "pm3.2i.mm"
include "axlowdimlem2.mm"
include "fun2.mm"
include "mp2an.mm"
include "axlowdimlem3.mm"
include "feq2d.mm"
include "mpbiri.mm"
include "cn.mm"
include "wb.mm"
include "eluz2nn.mm"
include "elee.mm"
include "syl.mm"
include "mpbird.mm"

theorem axlowdimlem5
  let cA: class A
  let cB: class B
  let cN: class N
  assume axlowdimlem4.1: |- A e. RR
  assume axlowdimlem4.2: |- B e. RR


  assert |- ( N e. ( ZZ>= ` 2 ) -> ( { <. 1 , A >. , <. 2 , B >. } u. ( ( 3 ... N ) X. { 0 } ) ) e. ( EE ` N ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    c1
    cA
    cop
    c2
    cB
    cop
    cpr
    #
    c3
    cN
    cfz
    co
    #
    cc0
    csn
    cxp
    #
    cun
    #
    cN
    cee
    cfv
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cr
    @4
    wf
    #
    @0
    @7
    c1
    c2
    cfz
    co
    #
    @2
    cun
    #
    cr
    @4
    wf
    #
    @8
    cr
    @1
    wf
    #
    @2
    cr
    @3
    wf
    #
    wa
    @8
    @2
    cin
    c0
    wceq
    @10
    @11
    @12
    cA
    cB
    axlowdimlem4.1
    axlowdimlem4.2
    axlowdimlem4
    cN
    axlowdimlem1
    pm3.2i
    cN
    axlowdimlem2
    @8
    @2
    cr
    @1
    @3
    fun2
    mp2an
    @0
    @6
    @9
    cr
    @4
    cN
    axlowdimlem3
    feq2d
    mpbiri
    @0
    cN
    cn
    wcel
    @5
    @7
    wb
    cN
    eluz2nn
    @4
    cN
    elee
    syl
    mpbird
end
