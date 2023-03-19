include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "cfv.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "unssd.mm"
include "ssun1.mm"
include "a1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "ssun2.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "lspssid.mm"
include "unss12.mm"
include "wceq.mm"
include "lspidm.mm"
include "sseqtrd.mm"
include "eqssd.mm"

theorem lspun
  let cT: class T
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let vt: setvar t
  assume lspss.v: |- V = ( Base ` W )
  assume lspss.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ T C_ V /\ U C_ V ) -> ( N ` ( T u. U ) ) = ( N ` ( ( N ` T ) u. ( N ` U ) ) ) )

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
    cU
    cun
    #
    cN
    cfv
    #
    cT
    cN
    cfv
    #
    cU
    cN
    cfv
    #
    cun
    #
    cN
    cfv
    #
    @3
    @0
    @8
    cV
    wss
    @4
    @8
    wss
    #
    @5
    @9
    wss
    @0
    @1
    @2
    simp1
    #
    @3
    @8
    @5
    cV
    @3
    @6
    @7
    @5
    @3
    @0
    @4
    cV
    wss
    #
    cT
    @4
    wss
    #
    @6
    @5
    wss
    @11
    @3
    cT
    cU
    cV
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    unssd
    #
    @13
    @3
    cT
    cU
    ssun1
    a1i
    cT
    @4
    cN
    cV
    cW
    lspss.v
    lspss.n
    lspss
    syl3anc
    @3
    @0
    @12
    cU
    @4
    wss
    #
    @7
    @5
    wss
    @11
    @16
    @17
    @3
    cU
    cT
    ssun2
    a1i
    cU
    @4
    cN
    cV
    cW
    lspss.v
    lspss.n
    lspss
    syl3anc
    unssd
    #
    @3
    @0
    @12
    @5
    cV
    wss
    #
    @11
    @16
    @4
    cN
    cV
    cW
    lspss.v
    lspss.n
    lspssv
    syl2anc
    #
    sstrd
    @3
    cT
    @6
    wss
    #
    cU
    @7
    wss
    #
    @10
    @3
    @0
    @1
    @21
    @11
    @14
    cT
    cN
    cV
    cW
    lspss.v
    lspss.n
    lspssid
    syl2anc
    @3
    @0
    @2
    @22
    @11
    @15
    cU
    cN
    cV
    cW
    lspss.v
    lspss.n
    lspssid
    syl2anc
    cT
    @6
    cU
    @7
    unss12
    syl2anc
    @4
    @8
    cN
    cV
    cW
    lspss.v
    lspss.n
    lspss
    syl3anc
    @3
    @9
    @5
    cN
    cfv
    #
    @5
    @3
    @0
    @19
    @8
    @5
    wss
    @9
    @23
    wss
    @11
    @20
    @18
    @8
    @5
    cN
    cV
    cW
    lspss.v
    lspss.n
    lspss
    syl3anc
    @3
    @0
    @12
    @23
    @5
    wceq
    @11
    @16
    @4
    cN
    cV
    cW
    lspss.v
    lspss.n
    lspidm
    syl2anc
    sseqtrd
    eqssd
end
