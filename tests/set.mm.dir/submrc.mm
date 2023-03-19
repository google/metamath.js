include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cpw.mm"
include "cin.mm"
include "submre.mm"
include "3adant3.mm"
include "simp1.mm"
include "simp3.mm"
include "mress.mm"
include "sstrd.mm"
include "mrcssidd.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "mrcsscl.mm"
include "3com23.mm"
include "fvex.mm"
include "elpw.mm"
include "sylibr.mm"
include "elind.mm"
include "syl3anc.mm"
include "inss1.mm"
include "sseldi.mm"
include "eqssd.mm"

theorem submrc
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cG: class G
  let cX: class X
  assume submrc.f: |- F = ( mrCls ` C )
  assume submrc.g: |- G = ( mrCls ` ( C i^i ~P D ) )


  assert |- ( ( C e. ( Moore ` X ) /\ D e. C /\ U C_ D ) -> ( G ` U ) = ( F ` U ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cD
    cC
    wcel
    #
    cU
    cD
    wss
    #
    w3a
    #
    cU
    cG
    cfv
    #
    cU
    cF
    cfv
    #
    @3
    cC
    cD
    cpw
    #
    cin
    #
    cD
    cmre
    cfv
    wcel
    #
    cU
    @5
    wss
    @5
    @7
    wcel
    @4
    @5
    wss
    @0
    @1
    @8
    @2
    cD
    cC
    cX
    submre
    3adant3
    #
    @3
    cC
    cU
    cF
    cX
    @0
    @1
    @2
    simp1
    #
    submrc.f
    @3
    cU
    cD
    cX
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    cD
    cX
    wss
    @2
    cC
    cD
    cX
    mress
    3adant3
    sstrd
    #
    mrcssidd
    @3
    cC
    @6
    @5
    @3
    @0
    cU
    cX
    wss
    @5
    cC
    wcel
    @10
    @12
    cC
    cU
    cF
    cX
    submrc.f
    mrccl
    syl2anc
    @3
    @5
    cD
    wss
    #
    @5
    @6
    wcel
    @0
    @2
    @1
    @13
    cC
    cU
    cF
    cD
    cX
    submrc.f
    mrcsscl
    3com23
    @5
    cD
    cU
    cF
    fvex
    elpw
    sylibr
    elind
    @7
    cU
    cG
    @5
    cD
    submrc.g
    mrcsscl
    syl3anc
    @3
    @0
    cU
    @4
    wss
    @4
    cC
    wcel
    @5
    @4
    wss
    @10
    @3
    @7
    cU
    cG
    cD
    @9
    submrc.g
    @11
    mrcssidd
    @3
    @7
    cC
    @4
    cC
    @6
    inss1
    @3
    @8
    @2
    @4
    @7
    wcel
    @9
    @11
    @7
    cU
    cG
    cD
    submrc.g
    mrccl
    syl2anc
    sseldi
    cC
    cU
    cF
    @4
    cX
    submrc.f
    mrcsscl
    syl3anc
    eqssd
end
