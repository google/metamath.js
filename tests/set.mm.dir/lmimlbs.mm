include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cima.mm"
include "clinds.mm"
include "cfv.mm"
include "clspn.mm"
include "cbs.mm"
include "wceq.mm"
include "clmhm.mm"
include "wf1.mm"
include "lmimlmhm.mm"
include "adantr.mm"
include "wf1o.mm"
include "eqid.mm"
include "lmimf1o.mm"
include "f1of1.mm"
include "syl.mm"
include "lbslinds.mm"
include "sseli.mm"
include "adantl.mm"
include "lindsmm2.mm"
include "syl3anc.mm"
include "lbssp.mm"
include "imaeq2d.mm"
include "wss.mm"
include "lbsss.mm"
include "lmhmlsp.mm"
include "syl2an.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "3syl.mm"
include "3eqtr3d.mm"
include "islbs4.mm"
include "sylanbrc.mm"

theorem lmimlbs
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  assume lmimlbs.j: |- J = ( LBasis ` S )
  assume lmimlbs.k: |- K = ( LBasis ` T )


  assert |- ( ( F e. ( S LMIso T ) /\ B e. J ) -> ( F " B ) e. K )

  proof
    cF
    cS
    cT
    clmim
    co
    wcel
    #
    cB
    cJ
    wcel
    #
    wa
    #
    cF
    cB
    cima
    #
    cT
    clinds
    cfv
    wcel
    #
    @3
    cT
    clspn
    cfv
    #
    cfv
    #
    cT
    cbs
    cfv
    #
    wceq
    @3
    cK
    wcel
    @2
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cS
    cbs
    cfv
    #
    @7
    cF
    wf1
    #
    cB
    cS
    clinds
    cfv
    #
    wcel
    #
    @4
    @0
    @8
    @1
    cS
    cT
    cF
    lmimlmhm
    #
    adantr
    @0
    @10
    @1
    @0
    @9
    @7
    cF
    wf1o
    #
    @10
    @9
    @7
    cS
    cT
    cF
    @9
    eqid
    #
    @7
    eqid
    #
    lmimf1o
    #
    @9
    @7
    cF
    f1of1
    syl
    adantr
    @1
    @12
    @0
    cJ
    @11
    cB
    cJ
    cS
    lmimlbs.j
    lbslinds
    sseli
    adantl
    @9
    @7
    cS
    cT
    cB
    cF
    @15
    @16
    lindsmm2
    syl3anc
    @2
    cF
    cB
    cS
    clspn
    cfv
    #
    cfv
    #
    cima
    #
    cF
    @9
    cima
    #
    @6
    @7
    @2
    @19
    @9
    cF
    @1
    @19
    @9
    wceq
    @0
    cB
    cJ
    @18
    @9
    cS
    @15
    lmimlbs.j
    @18
    eqid
    #
    lbssp
    adantl
    imaeq2d
    @0
    @8
    cB
    @9
    wss
    @20
    @6
    wceq
    @1
    @13
    cB
    cJ
    @9
    cS
    @15
    lmimlbs.j
    lbsss
    cS
    cT
    cB
    cF
    @18
    @5
    @9
    @15
    @22
    @5
    eqid
    #
    lmhmlsp
    syl2an
    @2
    @14
    @9
    @7
    cF
    wfo
    @21
    @7
    wceq
    @0
    @14
    @1
    @17
    adantr
    @9
    @7
    cF
    f1ofo
    @9
    @7
    cF
    foima
    3syl
    3eqtr3d
    @7
    cK
    @5
    cT
    @3
    @16
    lmimlbs.k
    @23
    islbs4
    sylanbrc
end
