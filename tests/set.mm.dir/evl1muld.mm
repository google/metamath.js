include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "crg.mm"
include "cpws.mm"
include "crh.mm"
include "ccrg.mm"
include "eqid.mm"
include "evl1rhm.mm"
include "syl.mm"
include "rhmrcl1.mm"
include "simpld.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "cof.mm"
include "cmulr.mm"
include "rhmmul.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "pwsmulrval.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "wfn.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "simprd.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "jca.mm"

theorem evl1muld
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume evl1addd.q: |- O = ( eval1 ` R )
  assume evl1addd.p: |- P = ( Poly1 ` R )
  assume evl1addd.b: |- B = ( Base ` R )
  assume evl1addd.u: |- U = ( Base ` P )
  assume evl1addd.1: |- ( ph -> R e. CRing )
  assume evl1addd.2: |- ( ph -> Y e. B )
  assume evl1addd.3: |- ( ph -> ( M e. U /\ ( ( O ` M ) ` Y ) = V ) )
  assume evl1addd.4: |- ( ph -> ( N e. U /\ ( ( O ` N ) ` Y ) = W ) )
  assume evl1muld.t: |- .xb = ( .r ` P )
  assume evl1muld.s: |- .x. = ( .r ` R )


  assert |- ( ph -> ( ( M .xb N ) e. U /\ ( ( O ` ( M .xb N ) ) ` Y ) = ( V .x. W ) ) )

  proof
    wph
    cM
    cN
    c.xb
    co
    #
    cU
    wcel
    #
    cY
    @0
    cO
    cfv
    #
    cfv
    #
    cV
    cW
    c.x
    co
    #
    wceq
    wph
    cP
    crg
    wcel
    #
    cM
    cU
    wcel
    #
    cN
    cU
    wcel
    #
    @1
    wph
    cO
    cP
    cR
    cB
    cpws
    co
    #
    crh
    co
    wcel
    #
    @5
    wph
    cR
    ccrg
    wcel
    @9
    evl1addd.1
    cB
    cP
    cR
    @8
    cO
    evl1addd.q
    evl1addd.p
    @8
    eqid
    #
    evl1addd.b
    evl1rhm
    syl
    #
    cP
    @8
    cO
    rhmrcl1
    syl
    wph
    @6
    cY
    cM
    cO
    cfv
    #
    cfv
    #
    cV
    wceq
    #
    evl1addd.3
    simpld
    #
    wph
    @7
    cY
    cN
    cO
    cfv
    #
    cfv
    #
    cW
    wceq
    #
    evl1addd.4
    simpld
    #
    cU
    cP
    c.xb
    cM
    cN
    evl1addd.u
    evl1muld.t
    ringcl
    syl3anc
    wph
    @3
    cY
    @12
    @16
    c.x
    cof
    co
    #
    cfv
    #
    @13
    @17
    c.x
    co
    #
    @4
    wph
    cY
    @2
    @20
    wph
    @2
    @12
    @16
    @8
    cmulr
    cfv
    #
    co
    #
    @20
    wph
    @9
    @6
    @7
    @2
    @24
    wceq
    @11
    @15
    @19
    cM
    cN
    cP
    @8
    c.xb
    @23
    cO
    cU
    evl1addd.u
    evl1muld.t
    @23
    eqid
    #
    rhmmul
    syl3anc
    wph
    @8
    cbs
    cfv
    #
    cR
    @23
    c.x
    @12
    @16
    cB
    ccrg
    cvv
    @8
    @10
    @26
    eqid
    #
    evl1addd.1
    cB
    cvv
    wcel
    #
    wph
    cB
    cR
    cbs
    cfv
    cvv
    evl1addd.b
    cR
    cbs
    fvex
    eqeltri
    a1i
    #
    wph
    cU
    @26
    cM
    cO
    wph
    @9
    cU
    @26
    cO
    wf
    @11
    cU
    @26
    cP
    @8
    cO
    evl1addd.u
    @27
    rhmf
    syl
    #
    @15
    ffvelrnd
    #
    wph
    cU
    @26
    cN
    cO
    @30
    @19
    ffvelrnd
    #
    evl1muld.s
    @25
    pwsmulrval
    eqtrd
    fveq1d
    wph
    @12
    cB
    wfn
    #
    @16
    cB
    wfn
    #
    @28
    cY
    cB
    wcel
    @21
    @22
    wceq
    wph
    cB
    cB
    @12
    wf
    @33
    wph
    cB
    cR
    cB
    @26
    ccrg
    @12
    @8
    cvv
    @10
    evl1addd.b
    @27
    evl1addd.1
    @29
    @31
    pwselbas
    cB
    cB
    @12
    ffn
    syl
    wph
    cB
    cB
    @16
    wf
    @34
    wph
    cB
    cR
    cB
    @26
    ccrg
    @16
    @8
    cvv
    @10
    evl1addd.b
    @27
    evl1addd.1
    @29
    @32
    pwselbas
    cB
    cB
    @16
    ffn
    syl
    @29
    evl1addd.2
    cB
    c.x
    @12
    @16
    cvv
    cY
    fnfvof
    syl22anc
    wph
    @13
    cV
    @17
    cW
    c.x
    wph
    @6
    @14
    evl1addd.3
    simprd
    wph
    @7
    @18
    evl1addd.4
    simprd
    oveq12d
    3eqtrd
    jca
end
