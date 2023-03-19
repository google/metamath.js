include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "ccj.mm"
include "ccom.mm"
include "cc.mm"
include "cv.mm"
include "cjcl.mm"
include "adantl.mm"
include "plyssc.mm"
include "sseli.mm"
include "plycj.mm"
include "cdgr.mm"
include "cn0.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "wf.mm"
include "cjf.mm"
include "coef3.mm"
include "fco.mm"
include "sylancr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "fvco3.mm"
include "sylan.mm"
include "cj0.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeq12d.mm"
include "wb.mm"
include "ffvelrnda.mm"
include "0cnd.mm"
include "cj11.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "necon3bid.mm"
include "dgrub2.mm"
include "plyco0.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "mpbird.mm"
include "plycjlem.mm"
include "coeeq.mm"

theorem coecj
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z
  let wph: wff ph
  assume plycj.1: |- N = ( deg ` F )
  assume plycj.2: |- G = ( ( * o. F ) o. * )
  assume coecj.3: |- A = ( coeff ` F )


  assert |- ( F e. ( Poly ` S ) -> ( coeff ` G ) = ( * o. A ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    vz
    ccj
    cA
    ccom
    #
    cc
    vk
    cG
    cN
    @1
    vx
    cc
    cF
    cG
    cN
    plycj.1
    plycj.2
    vx
    cv
    #
    cc
    wcel
    @3
    ccj
    cfv
    cc
    wcel
    @1
    @3
    cjcl
    adantl
    @0
    cc
    cply
    cfv
    cF
    cS
    plyssc
    sseli
    plycj
    @1
    cN
    cF
    cdgr
    cfv
    cn0
    plycj.1
    cS
    cF
    dgrcl
    syl5eqel
    #
    @1
    cc
    cc
    ccj
    wf
    cn0
    cc
    cA
    wf
    #
    cn0
    cc
    @2
    wf
    #
    cjf
    cA
    cS
    cF
    coecj.3
    coef3
    #
    cn0
    cc
    cc
    ccj
    cA
    fco
    sylancr
    #
    @1
    @2
    cN
    c1
    caddc
    co
    cuz
    cfv
    #
    cima
    cc0
    csn
    #
    wceq
    #
    vk
    cv
    #
    @2
    cfv
    #
    cc0
    wne
    #
    @12
    cN
    cle
    wbr
    #
    wi
    #
    vk
    cn0
    wral
    #
    @1
    @16
    vk
    cn0
    @1
    @12
    cn0
    wcel
    #
    wa
    #
    @14
    @12
    cA
    cfv
    #
    cc0
    wne
    #
    @15
    @19
    @13
    cc0
    @20
    cc0
    @19
    @13
    cc0
    wceq
    @20
    ccj
    cfv
    #
    cc0
    ccj
    cfv
    #
    wceq
    #
    @20
    cc0
    wceq
    #
    @19
    @13
    @22
    cc0
    @23
    @1
    @5
    @18
    @13
    @22
    wceq
    @7
    cn0
    cc
    @12
    ccj
    cA
    fvco3
    sylan
    cc0
    @23
    wceq
    @19
    @23
    cc0
    cj0
    eqcomi
    a1i
    eqeq12d
    @19
    @20
    cc
    wcel
    cc0
    cc
    wcel
    @24
    @25
    wb
    @1
    cn0
    cc
    @12
    cA
    @7
    ffvelrnda
    @19
    0cnd
    @20
    cc0
    cj11
    syl2anc
    bitrd
    necon3bid
    @1
    @21
    @15
    wi
    #
    vk
    cn0
    @1
    cA
    @9
    cima
    @10
    wceq
    #
    @26
    vk
    cn0
    wral
    #
    cA
    cS
    cF
    cN
    coecj.3
    plycj.1
    dgrub2
    @1
    cN
    cn0
    wcel
    #
    @5
    @27
    @28
    wb
    @4
    @7
    cA
    vk
    cN
    plyco0
    syl2anc
    mpbid
    r19.21bi
    sylbid
    ralrimiva
    @1
    @29
    @6
    @11
    @17
    wb
    @4
    @8
    @2
    vk
    cN
    plyco0
    syl2anc
    mpbird
    vz
    cA
    cS
    vk
    cF
    cG
    cN
    plycj.1
    plycj.2
    coecj.3
    plycjlem
    coeeq
end
