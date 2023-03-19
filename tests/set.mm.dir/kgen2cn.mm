include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ckgen.mm"
include "cfv.mm"
include "cuni.mm"
include "ctopon.mm"
include "wss.mm"
include "ctop.mm"
include "cntop1.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "kgentopon.mm"
include "syl.mm"
include "kgenss.mm"
include "cnss1.mm"
include "syl2anc.mm"
include "crn.mm"
include "wceq.mm"
include "wfn.mm"
include "wf.mm"
include "kgenf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "cntop2.mm"
include "kgencn3.mm"
include "sseqtrd.mm"
include "id.mm"
include "sseldd.mm"

theorem kgen2cn
  let cF: class F
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. ( J Cn K ) -> F e. ( ( kGen ` J ) Cn ( kGen ` K ) ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    @0
    cJ
    ckgen
    cfv
    #
    cK
    ckgen
    cfv
    ccn
    co
    #
    cF
    @1
    @0
    @2
    cK
    ccn
    co
    #
    @3
    @1
    @2
    cJ
    cuni
    #
    ctopon
    cfv
    #
    wcel
    #
    cJ
    @2
    wss
    #
    @0
    @4
    wss
    @1
    cJ
    @6
    wcel
    #
    @7
    @1
    cJ
    ctop
    wcel
    #
    @9
    cF
    cJ
    cK
    cntop1
    #
    cJ
    @5
    @5
    eqid
    #
    toptopon
    sylib
    cJ
    @5
    kgentopon
    syl
    @1
    @10
    @8
    @11
    cJ
    kgenss
    syl
    cJ
    @2
    cK
    @5
    @12
    cnss1
    syl2anc
    @1
    @2
    ckgen
    crn
    wcel
    #
    cK
    ctop
    wcel
    @4
    @3
    wceq
    @1
    ckgen
    ctop
    wfn
    #
    @10
    @13
    ctop
    ctop
    ckgen
    wf
    @14
    kgenf
    ctop
    ctop
    ckgen
    ffn
    ax-mp
    @11
    ctop
    cJ
    ckgen
    fnfvelrn
    sylancr
    cF
    cJ
    cK
    cntop2
    @2
    cK
    kgencn3
    syl2anc
    sseqtrd
    @1
    id
    sseldd
end
