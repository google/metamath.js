include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "eleq1.mm"
include "id.mm"
include "ifbieq1d.mm"
include "iftrue.mm"
include "adantr.mm"
include "sylan9eqr.mm"
include "elfznn.mm"
include "adantl.mm"
include "simpl.mm"
include "fvmptd.mm"
include "simprr.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "1nn.mm"
include "cuz.mm"
include "elnnuz.mm"
include "eluzfz1.mm"
include "sylbi.mm"
include "pm2.61ian.mm"

theorem fvprmselelfz
  let vm: setvar m
  let cF: class F
  let cN: class N
  let cX: class X
  assume fvprmselelfz.f: |- F = ( m e. NN |-> if ( m e. Prime , m , 1 ) )

  disjoint N m
  disjoint X m
  assert |- ( ( N e. NN /\ X e. ( 1 ... N ) ) -> ( F ` X ) e. ( 1 ... N ) )

  proof
    cX
    cprime
    wcel
    #
    cN
    cn
    wcel
    #
    cX
    c1
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    cX
    cF
    cfv
    #
    @2
    wcel
    @0
    @4
    wa
    #
    @5
    cX
    @2
    @6
    vm
    cX
    vm
    cv
    #
    cprime
    wcel
    #
    @7
    c1
    cif
    #
    cX
    cn
    cF
    cprime
    cF
    vm
    cn
    @9
    cmpt
    wceq
    #
    @6
    fvprmselelfz.f
    a1i
    @7
    cX
    wceq
    #
    @6
    @9
    @0
    cX
    c1
    cif
    #
    cX
    @11
    @8
    @0
    @7
    cX
    c1
    @7
    cX
    cprime
    eleq1
    @11
    id
    ifbieq1d
    #
    @0
    @12
    cX
    wceq
    @4
    @0
    cX
    c1
    iftrue
    adantr
    sylan9eqr
    @4
    cX
    cn
    wcel
    #
    @0
    @3
    @14
    @1
    cX
    cN
    elfznn
    adantl
    #
    adantl
    @0
    @4
    simpl
    fvmptd
    @0
    @1
    @3
    simprr
    eqeltrd
    @0
    wn
    #
    @4
    wa
    #
    @5
    c1
    @2
    @17
    vm
    cX
    @9
    c1
    cn
    cF
    cn
    @10
    @17
    fvprmselelfz.f
    a1i
    @11
    @17
    @9
    @12
    c1
    @13
    @16
    @12
    c1
    wceq
    @4
    @0
    cX
    c1
    iffalse
    adantr
    sylan9eqr
    @4
    @14
    @16
    @15
    adantl
    c1
    cn
    wcel
    @17
    1nn
    a1i
    fvmptd
    @4
    c1
    @2
    wcel
    #
    @16
    @1
    @18
    @3
    @1
    cN
    c1
    cuz
    cfv
    wcel
    @18
    cN
    elnnuz
    c1
    cN
    eluzfz1
    sylbi
    adantr
    adantl
    eqeltrd
    pm2.61ian
end
