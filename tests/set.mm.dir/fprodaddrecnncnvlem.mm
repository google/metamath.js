include "ccom.mm"
include "cc0.mm"
include "cfv.mm"
include "cli.mm"
include "wbr.mm"
include "cprod.mm"
include "cc.mm"
include "c1.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "fprodadd2cncf.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wcel.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "nnrp.mm"
include "rpdivcld.mm"
include "rpcnd.mm"
include "adantl.mm"
include "fmptd.mm"
include "cmpt.mm"
include "1cnd.mm"
include "divcnv.mm"
include "syl.mm"
include "wceq.mm"
include "breq1d.mm"
include "mpbird.mm"
include "0cnd.mm"
include "climcncf.mm"
include "wf.mm"
include "caddc.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "cfn.mm"
include "adantr.mm"
include "adantlr.mm"
include "simplr.mm"
include "addcld.mm"
include "fprodclf.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "id.mm"
include "fvmpt2.mm"
include "fveq2d.mm"
include "cvv.mm"
include "oveq2.mm"
include "prodeq2ad.mm"
include "prodex.mm"
include "fvmptd.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "ad2antlr.mm"
include "addid1d.mm"
include "ex.mm"
include "ralrimi.mm"
include "prodeq2d.mm"
include "breq12d.mm"
include "mpbid.mm"

theorem fprodaddrecnncnvlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  assume fprodaddrecnncnvlem.k: |- F/ k ph
  assume fprodaddrecnncnvlem.a: |- ( ph -> A e. Fin )
  assume fprodaddrecnncnvlem.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodaddrecnncnvlem.s: |- S = ( n e. NN |-> prod_ k e. A ( B + ( 1 / n ) ) )
  assume fprodaddrecnncnvlem.f: |- F = ( x e. CC |-> prod_ k e. A ( B + x ) )
  assume fprodaddrecnncnvlem.g: |- G = ( n e. NN |-> ( 1 / n ) )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint F n
  disjoint G n
  disjoint k n
  disjoint n x
  disjoint n ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S ~~> prod_ k e. A B )

  proof
    wph
    cF
    cG
    ccom
    #
    cc0
    cF
    cfv
    #
    cli
    wbr
    cS
    cA
    cB
    vk
    cprod
    #
    cli
    wbr
    wph
    cc
    cc
    cc0
    cF
    cG
    c1
    cn
    nnuz
    wph
    1zzd
    wph
    vx
    cA
    cB
    vk
    cF
    fprodaddrecnncnvlem.k
    fprodaddrecnncnvlem.a
    fprodaddrecnncnvlem.b
    fprodaddrecnncnvlem.f
    fprodadd2cncf
    wph
    vn
    cn
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cc
    cG
    @3
    cn
    wcel
    #
    @4
    cc
    wcel
    #
    wph
    @5
    @4
    @5
    c1
    @3
    c1
    crp
    wcel
    @5
    1rp
    a1i
    @3
    nnrp
    rpdivcld
    rpcnd
    #
    adantl
    #
    fprodaddrecnncnvlem.g
    fmptd
    #
    wph
    cG
    cc0
    cli
    wbr
    vn
    cn
    @4
    cmpt
    #
    cc0
    cli
    wbr
    #
    wph
    c1
    cc
    wcel
    @11
    wph
    1cnd
    c1
    vn
    divcnv
    syl
    wph
    cG
    @10
    cc0
    cli
    cG
    @10
    wceq
    wph
    fprodaddrecnncnvlem.g
    a1i
    breq1d
    mpbird
    wph
    0cnd
    #
    climcncf
    wph
    @0
    cS
    @1
    @2
    cli
    wph
    @0
    vn
    cn
    @3
    cG
    cfv
    #
    cF
    cfv
    #
    cmpt
    #
    cS
    wph
    cc
    cc
    cF
    wf
    cn
    cc
    cG
    wf
    @0
    @15
    wceq
    wph
    vx
    cc
    cA
    cB
    vx
    cv
    #
    caddc
    co
    #
    vk
    cprod
    #
    cc
    cF
    wph
    @16
    cc
    wcel
    #
    wa
    #
    cA
    @17
    vk
    wph
    @19
    vk
    fprodaddrecnncnvlem.k
    @19
    vk
    nfv
    nfan
    wph
    cA
    cfn
    wcel
    @19
    fprodaddrecnncnvlem.a
    adantr
    @20
    vk
    cv
    cA
    wcel
    #
    wa
    cB
    @16
    wph
    @21
    cB
    cc
    wcel
    @19
    fprodaddrecnncnvlem.b
    adantlr
    wph
    @19
    @21
    simplr
    addcld
    fprodclf
    fprodaddrecnncnvlem.f
    fmptd
    @9
    vn
    cF
    cG
    cn
    cc
    cc
    fcompt
    syl2anc
    wph
    cS
    vn
    cn
    cA
    cB
    @4
    caddc
    co
    #
    vk
    cprod
    #
    cmpt
    #
    @15
    cS
    @24
    wceq
    wph
    fprodaddrecnncnvlem.s
    a1i
    wph
    vn
    cn
    @23
    @14
    wph
    @5
    wa
    #
    @14
    @4
    cF
    cfv
    #
    @23
    @5
    @14
    @26
    wceq
    wph
    @5
    @13
    @4
    cF
    @5
    @5
    @6
    @13
    @4
    wceq
    @5
    id
    @7
    vn
    cn
    @4
    cc
    cG
    fprodaddrecnncnvlem.g
    fvmpt2
    syl2anc
    fveq2d
    adantl
    @25
    vx
    @4
    @18
    @23
    cc
    cF
    cvv
    cF
    vx
    cc
    @18
    cmpt
    wceq
    #
    @25
    fprodaddrecnncnvlem.f
    a1i
    @16
    @4
    wceq
    #
    @18
    @23
    wceq
    @25
    @28
    cA
    @17
    @22
    vk
    @16
    @4
    cB
    caddc
    oveq2
    prodeq2ad
    adantl
    @8
    @23
    cvv
    wcel
    @25
    cA
    @22
    vk
    prodex
    a1i
    fvmptd
    eqtr2d
    mpteq2dva
    eqtrd
    eqtr4d
    wph
    vx
    cc0
    @18
    @2
    cc
    cF
    cvv
    @27
    wph
    fprodaddrecnncnvlem.f
    a1i
    wph
    @16
    cc0
    wceq
    #
    wa
    #
    cA
    @17
    cB
    vk
    @30
    @17
    cB
    wceq
    #
    vk
    cA
    wph
    @29
    vk
    fprodaddrecnncnvlem.k
    @29
    vk
    nfv
    nfan
    @30
    @21
    @31
    @30
    @21
    wa
    @17
    cB
    cc0
    caddc
    co
    #
    cB
    @29
    @17
    @32
    wceq
    wph
    @21
    @16
    cc0
    cB
    caddc
    oveq2
    ad2antlr
    wph
    @21
    @32
    cB
    wceq
    @29
    wph
    @21
    wa
    cB
    fprodaddrecnncnvlem.b
    addid1d
    adantlr
    eqtrd
    ex
    ralrimi
    prodeq2d
    @12
    @2
    cvv
    wcel
    wph
    cA
    cB
    vk
    prodex
    a1i
    fvmptd
    breq12d
    mpbid
end
