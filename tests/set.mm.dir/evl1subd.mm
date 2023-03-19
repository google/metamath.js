include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "cpws.mm"
include "cghm.mm"
include "crh.mm"
include "ccrg.mm"
include "eqid.mm"
include "evl1rhm.mm"
include "syl.mm"
include "rhmghm.mm"
include "ghmgrp1.mm"
include "simpld.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "cof.mm"
include "csg.mm"
include "ghmsub.mm"
include "cvv.mm"
include "cbs.mm"
include "crg.mm"
include "crngring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "pwssub.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "wfn.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fnfvof.mm"
include "simprd.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "jca.mm"

theorem evl1subd
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cU: class U
  let cM: class M
  let c.mi: class .-
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
  assume evl1subd.s: |- .- = ( -g ` P )
  assume evl1subd.d: |- D = ( -g ` R )


  assert |- ( ph -> ( ( M .- N ) e. U /\ ( ( O ` ( M .- N ) ) ` Y ) = ( V D W ) ) )

  proof
    wph
    cM
    cN
    c.mi
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
    cD
    co
    #
    wceq
    wph
    cP
    cgrp
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
    cghm
    co
    wcel
    #
    @5
    wph
    cO
    cP
    @8
    crh
    co
    wcel
    #
    @9
    wph
    cR
    ccrg
    wcel
    #
    @10
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
    rhmghm
    syl
    #
    cP
    @8
    cO
    ghmgrp1
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
    c.mi
    cM
    cN
    evl1addd.u
    evl1subd.s
    grpsubcl
    syl3anc
    wph
    @3
    cY
    @15
    @19
    cD
    cof
    co
    #
    cfv
    #
    @16
    @20
    cD
    co
    #
    @4
    wph
    cY
    @2
    @23
    wph
    @2
    @15
    @19
    @8
    csg
    cfv
    #
    co
    #
    @23
    wph
    @9
    @6
    @7
    @2
    @27
    wceq
    @14
    @18
    @22
    cU
    cP
    @8
    cM
    cO
    c.mi
    @26
    cN
    evl1addd.u
    evl1subd.s
    @26
    eqid
    #
    ghmsub
    syl3anc
    wph
    cR
    cgrp
    wcel
    #
    cB
    cvv
    wcel
    #
    @15
    @8
    cbs
    cfv
    #
    wcel
    @19
    @31
    wcel
    @27
    @23
    wceq
    wph
    @11
    cR
    crg
    wcel
    @29
    evl1addd.1
    cR
    crngring
    cR
    ringgrp
    3syl
    @30
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
    @31
    cM
    cO
    wph
    @10
    cU
    @31
    cO
    wf
    @13
    cU
    @31
    cP
    @8
    cO
    evl1addd.u
    @31
    eqid
    #
    rhmf
    syl
    #
    @18
    ffvelrnd
    #
    wph
    cU
    @31
    cN
    cO
    @34
    @22
    ffvelrnd
    #
    @31
    cR
    @15
    @19
    cB
    cD
    @26
    cvv
    @8
    @12
    @33
    evl1subd.d
    @28
    pwssub
    syl22anc
    eqtrd
    fveq1d
    wph
    @15
    cB
    wfn
    #
    @19
    cB
    wfn
    #
    @30
    cY
    cB
    wcel
    @24
    @25
    wceq
    wph
    cB
    cB
    @15
    wf
    @37
    wph
    cB
    cR
    cB
    @31
    ccrg
    @15
    @8
    cvv
    @12
    evl1addd.b
    @33
    evl1addd.1
    @32
    @35
    pwselbas
    cB
    cB
    @15
    ffn
    syl
    wph
    cB
    cB
    @19
    wf
    @38
    wph
    cB
    cR
    cB
    @31
    ccrg
    @19
    @8
    cvv
    @12
    evl1addd.b
    @33
    evl1addd.1
    @32
    @36
    pwselbas
    cB
    cB
    @19
    ffn
    syl
    @32
    evl1addd.2
    cB
    cD
    @15
    @19
    cvv
    cY
    fnfvof
    syl22anc
    wph
    @16
    cV
    @20
    cW
    cD
    wph
    @6
    @17
    evl1addd.3
    simprd
    wph
    @7
    @21
    evl1addd.4
    simprd
    oveq12d
    3eqtrd
    jca
end
