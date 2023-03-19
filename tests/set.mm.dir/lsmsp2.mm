include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cun.mm"
include "clss.mm"
include "wceq.mm"
include "simp1.mm"
include "eqid.mm"
include "lspcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "lsmsp.mm"
include "syl3anc.mm"
include "lspun.mm"
include "eqtr4d.mm"

theorem lsmsp2
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  assume lsmsp2.v: |- V = ( Base ` W )
  assume lsmsp2.n: |- N = ( LSpan ` W )
  assume lsmsp2.p: |- .(+) = ( LSSum ` W )


  assert |- ( ( W e. LMod /\ T C_ V /\ U C_ V ) -> ( ( N ` T ) .(+) ( N ` U ) ) = ( N ` ( T u. U ) ) )

  proof
    cW
    clmod
    wcel
    #
    cT
    cV
    wss
    #
    cU
    cV
    wss
    #
    w3a
    #
    cT
    cN
    cfv
    #
    cU
    cN
    cfv
    #
    c.po
    co
    #
    @4
    @5
    cun
    cN
    cfv
    #
    cT
    cU
    cun
    cN
    cfv
    @3
    @0
    @4
    cW
    clss
    cfv
    #
    wcel
    #
    @5
    @8
    wcel
    #
    @6
    @7
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @9
    @2
    @8
    cT
    cN
    cV
    cW
    lsmsp2.v
    @8
    eqid
    #
    lsmsp2.n
    lspcl
    3adant3
    @0
    @2
    @10
    @1
    @8
    cU
    cN
    cV
    cW
    lsmsp2.v
    @11
    lsmsp2.n
    lspcl
    3adant2
    c.po
    @8
    @4
    @5
    cN
    cW
    @11
    lsmsp2.n
    lsmsp2.p
    lsmsp
    syl3anc
    cT
    cU
    cN
    cV
    cW
    lsmsp2.v
    lsmsp2.n
    lspun
    eqtr4d
end
