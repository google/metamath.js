include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cdgr.mm"
include "caddc.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "dgrmul2.mm"
include "ad2ant2r.mm"
include "cc.mm"
include "cn0.mm"
include "ccoe.mm"
include "cc0.mm"
include "plymulcl.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "ad2antrr.mm"
include "ad2antrl.mm"
include "nn0addcld.mm"
include "eqid.mm"
include "coemulhi.mm"
include "wf.mm"
include "coef3.mm"
include "ffvelrnd.mm"
include "dgreq0.mm"
include "necon3bid.mm"
include "biimpa.mm"
include "adantr.mm"
include "adantl.mm"
include "mulne0d.mm"
include "eqnetrd.mm"
include "dgrub.mm"
include "syl3anc.mm"
include "syl.mm"
include "nn0red.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem dgrmul
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume dgradd.1: |- M = ( deg ` F )
  assume dgradd.2: |- N = ( deg ` G )


  assert |- ( ( ( F e. ( Poly ` S ) /\ F =/= 0p ) /\ ( G e. ( Poly ` S ) /\ G =/= 0p ) ) -> ( deg ` ( F oF x. G ) ) = ( M + N ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cF
    c0p
    wne
    #
    wa
    #
    cG
    @0
    wcel
    #
    cG
    c0p
    wne
    #
    wa
    #
    wa
    #
    cF
    cG
    cmul
    cof
    co
    #
    cdgr
    cfv
    #
    cM
    cN
    caddc
    co
    #
    wceq
    @9
    @10
    cle
    wbr
    #
    @10
    @9
    cle
    wbr
    #
    @1
    @4
    @11
    @2
    @5
    cS
    cF
    cG
    cM
    cN
    dgradd.1
    dgradd.2
    dgrmul2
    ad2ant2r
    @7
    @8
    cc
    cply
    cfv
    wcel
    #
    @10
    cn0
    wcel
    @10
    @8
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    @12
    @1
    @4
    @13
    @2
    @5
    cS
    cF
    cG
    plymulcl
    ad2ant2r
    #
    @7
    cM
    cN
    @1
    cM
    cn0
    wcel
    @2
    @6
    @1
    cM
    cF
    cdgr
    cfv
    cn0
    dgradd.1
    cS
    cF
    dgrcl
    syl5eqel
    ad2antrr
    #
    @4
    cN
    cn0
    wcel
    @3
    @5
    @4
    cN
    cG
    cdgr
    cfv
    cn0
    dgradd.2
    cS
    cG
    dgrcl
    syl5eqel
    ad2antrl
    #
    nn0addcld
    #
    @7
    @15
    cM
    cF
    ccoe
    cfv
    #
    cfv
    #
    cN
    cG
    ccoe
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cc0
    @1
    @4
    @15
    @24
    wceq
    @2
    @5
    @20
    @22
    cS
    cF
    cG
    cM
    cN
    @20
    eqid
    #
    @22
    eqid
    #
    dgradd.1
    dgradd.2
    coemulhi
    ad2ant2r
    @7
    @21
    @23
    @7
    cn0
    cc
    cM
    @20
    @1
    cn0
    cc
    @20
    wf
    @2
    @6
    @20
    cS
    cF
    @25
    coef3
    ad2antrr
    @17
    ffvelrnd
    @7
    cn0
    cc
    cN
    @22
    @4
    cn0
    cc
    @22
    wf
    @3
    @5
    @22
    cS
    cG
    @26
    coef3
    ad2antrl
    @18
    ffvelrnd
    @3
    @21
    cc0
    wne
    #
    @6
    @1
    @2
    @27
    @1
    cF
    c0p
    @21
    cc0
    @20
    cS
    cF
    cM
    dgradd.1
    @25
    dgreq0
    necon3bid
    biimpa
    adantr
    @6
    @23
    cc0
    wne
    #
    @3
    @4
    @5
    @28
    @4
    cG
    c0p
    @23
    cc0
    @22
    cS
    cG
    cN
    dgradd.2
    @26
    dgreq0
    necon3bid
    biimpa
    adantl
    mulne0d
    eqnetrd
    @14
    cc
    @8
    @10
    @9
    @14
    eqid
    @9
    eqid
    dgrub
    syl3anc
    @7
    @9
    @10
    @7
    @9
    @7
    @13
    @9
    cn0
    wcel
    @16
    cc
    @8
    dgrcl
    syl
    nn0red
    @7
    @10
    @19
    nn0red
    letri3d
    mpbir2and
end
