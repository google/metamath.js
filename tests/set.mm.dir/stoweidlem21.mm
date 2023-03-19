include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "csn.mm"
include "cxp.mm"
include "caddc.mm"
include "cmpt.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "mpteq2da.mm"
include "syl5eq.mm"
include "fconstmpt.mm"
include "nfcv.mm"
include "eqidd.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "wi.mm"
include "nfeq2.mm"
include "simpl.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "expcom.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "syl5eqel.mm"
include "nfsn.mm"
include "nfxp.mm"
include "stoweidlem8.mm"
include "mpd3an23.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "wf.mm"
include "feq1.mm"
include "rspccva.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "readdcld.mm"
include "fvmpt2.mm"
include "oveq1d.mm"
include "recnd.mm"
include "cc.mm"
include "subsub3d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "r19.21bi.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "fveq1.mm"
include "breq1d.mm"
include "ralbid.mm"
include "rspcev.mm"

theorem stoweidlem21
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let vs: setvar s
  let vk: setvar k
  assume stoweidlem21.1: |- F/_ t G
  assume stoweidlem21.2: |- F/_ t H
  assume stoweidlem21.3: |- F/_ t S
  assume stoweidlem21.4: |- F/ t ph
  assume stoweidlem21.5: |- G = ( t e. T |-> ( ( H ` t ) + S ) )
  assume stoweidlem21.6: |- ( ph -> F : T --> RR )
  assume stoweidlem21.7: |- ( ph -> S e. RR )
  assume stoweidlem21.8: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem21.9: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem21.10: |- ( ph -> A. f e. A f : T --> RR )
  assume stoweidlem21.11: |- ( ph -> H e. A )
  assume stoweidlem21.12: |- ( ph -> A. t e. T ( abs ` ( ( H ` t ) - ( ( F ` t ) - S ) ) ) < E )

  disjoint f g
  disjoint f t
  disjoint T f
  disjoint g t
  disjoint T g
  disjoint T t
  disjoint A f
  disjoint A g
  disjoint E f
  disjoint E g
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint H f
  disjoint H g
  disjoint f ph
  disjoint g ph
  disjoint S g
  disjoint t x
  disjoint T x
  disjoint A x
  disjoint S x
  disjoint ph x
  disjoint S s
  disjoint T s
  disjoint k x
  assert |- ( ph -> E. f e. A A. t e. T ( abs ` ( ( f ` t ) - ( F ` t ) ) ) < E )

  proof
    wph
    cG
    cA
    wcel
    vt
    cv
    #
    cG
    cfv
    #
    @0
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    vt
    cT
    wral
    #
    @0
    vf
    cv
    #
    cfv
    #
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    vt
    cT
    wral
    #
    vf
    cA
    wrex
    wph
    cG
    vt
    cT
    @0
    cH
    cfv
    #
    @0
    cT
    cS
    csn
    #
    cxp
    #
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cA
    wph
    cG
    vt
    cT
    @13
    cS
    caddc
    co
    #
    cmpt
    @18
    stoweidlem21.5
    wph
    vt
    cT
    @19
    @17
    stoweidlem21.4
    wph
    @0
    cT
    wcel
    #
    wa
    #
    cS
    @16
    @13
    caddc
    @21
    @16
    cS
    wph
    cS
    cr
    wcel
    #
    @20
    @16
    cS
    wceq
    stoweidlem21.7
    cT
    cS
    @0
    cr
    fvconst2g
    sylan
    eqcomd
    oveq2d
    mpteq2da
    syl5eq
    wph
    cH
    cA
    wcel
    #
    @15
    cA
    wcel
    @18
    cA
    wcel
    stoweidlem21.11
    wph
    @15
    vt
    cT
    cS
    cmpt
    #
    cA
    @15
    vs
    cT
    cS
    cmpt
    @24
    vs
    cT
    cS
    fconstmpt
    vs
    vt
    cT
    cS
    cS
    stoweidlem21.3
    vs
    cS
    nfcv
    vs
    cv
    @0
    wceq
    cS
    eqidd
    cbvmpt
    eqtri
    @22
    wph
    @24
    cA
    wcel
    #
    stoweidlem21.7
    wph
    vt
    cT
    vx
    cv
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    @25
    wi
    vx
    cS
    cr
    @26
    cS
    wceq
    #
    @28
    @25
    wph
    @29
    @27
    @24
    cA
    @29
    vt
    cT
    @26
    cS
    vt
    @26
    cS
    stoweidlem21.3
    nfeq2
    @29
    @20
    simpl
    mpteq2da
    eleq1d
    imbi2d
    wph
    @26
    cr
    wcel
    @28
    stoweidlem21.9
    expcom
    vtoclga
    mpcom
    syl5eqel
    wph
    vt
    cA
    cT
    vf
    vg
    cH
    @15
    stoweidlem21.8
    stoweidlem21.2
    vt
    cT
    @14
    vt
    cT
    nfcv
    vt
    cS
    stoweidlem21.3
    nfsn
    nfxp
    stoweidlem8
    mpd3an23
    eqeltrd
    wph
    @5
    vt
    cT
    stoweidlem21.4
    wph
    @20
    @5
    @21
    @4
    @13
    @2
    cS
    cmin
    co
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    @21
    @3
    @30
    cabs
    @21
    @3
    @19
    @2
    cmin
    co
    @30
    @21
    @1
    @19
    @2
    cmin
    @21
    @20
    @19
    cr
    wcel
    @1
    @19
    wceq
    wph
    @20
    simpr
    @21
    @13
    cS
    wph
    cT
    cr
    @0
    cH
    wph
    cT
    cr
    @7
    wf
    #
    vf
    cA
    wral
    @23
    cT
    cr
    cH
    wf
    #
    stoweidlem21.10
    stoweidlem21.11
    @32
    @33
    vf
    cH
    cA
    cT
    cr
    @7
    cH
    feq1
    rspccva
    syl2anc
    ffvelrnda
    #
    wph
    @22
    @20
    stoweidlem21.7
    adantr
    readdcld
    vt
    cT
    @19
    cr
    cG
    stoweidlem21.5
    fvmpt2
    syl2anc
    oveq1d
    @21
    @13
    @2
    cS
    @21
    @13
    @34
    recnd
    @21
    @2
    wph
    cT
    cr
    @0
    cF
    stoweidlem21.6
    ffvelrnda
    recnd
    wph
    cS
    cc
    wcel
    @20
    wph
    cS
    stoweidlem21.7
    recnd
    adantr
    subsub3d
    eqtr4d
    fveq2d
    wph
    @31
    cE
    clt
    wbr
    vt
    cT
    stoweidlem21.12
    r19.21bi
    eqbrtrd
    ex
    ralrimi
    @12
    @6
    vf
    cG
    cA
    @7
    cG
    wceq
    #
    @11
    @5
    vt
    cT
    vt
    @7
    cG
    stoweidlem21.1
    nfeq2
    @35
    @10
    @4
    cE
    clt
    @35
    @9
    @3
    cabs
    @35
    @8
    @1
    @2
    cmin
    @0
    @7
    cG
    fveq1
    oveq1d
    fveq2d
    breq1d
    ralbid
    rspcev
    syl2anc
end
