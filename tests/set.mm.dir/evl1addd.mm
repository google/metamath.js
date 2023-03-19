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
include "grpcl.mm"
include "syl3anc.mm"
include "cof.mm"
include "cplusg.mm"
include "ghmlin.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "pwsplusgval.mm"
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

theorem evl1addd
  let wph: wff ph
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
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
  assume evl1addd.g: |- .+b = ( +g ` P )
  assume evl1addd.a: |- .+ = ( +g ` R )


  assert |- ( ph -> ( ( M .+b N ) e. U /\ ( ( O ` ( M .+b N ) ) ` Y ) = ( V .+ W ) ) )

  proof
    wph
    cM
    cN
    c.pb
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
    c.pl
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
    c.pb
    cP
    cM
    cN
    evl1addd.u
    evl1addd.g
    grpcl
    syl3anc
    wph
    @3
    cY
    @14
    @18
    c.pl
    cof
    co
    #
    cfv
    #
    @15
    @19
    c.pl
    co
    #
    @4
    wph
    cY
    @2
    @22
    wph
    @2
    @14
    @18
    @8
    cplusg
    cfv
    #
    co
    #
    @22
    wph
    @9
    @6
    @7
    @2
    @26
    wceq
    @13
    @17
    @21
    c.pb
    @25
    cP
    @8
    cM
    cO
    cN
    cU
    evl1addd.u
    evl1addd.g
    @25
    eqid
    #
    ghmlin
    syl3anc
    wph
    @8
    cbs
    cfv
    #
    c.pl
    @25
    cR
    @14
    @18
    cB
    ccrg
    cvv
    @8
    @11
    @28
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
    @28
    cM
    cO
    wph
    @10
    cU
    @28
    cO
    wf
    @12
    cU
    @28
    cP
    @8
    cO
    evl1addd.u
    @29
    rhmf
    syl
    #
    @17
    ffvelrnd
    #
    wph
    cU
    @28
    cN
    cO
    @32
    @21
    ffvelrnd
    #
    evl1addd.a
    @27
    pwsplusgval
    eqtrd
    fveq1d
    wph
    @14
    cB
    wfn
    #
    @18
    cB
    wfn
    #
    @30
    cY
    cB
    wcel
    @23
    @24
    wceq
    wph
    cB
    cB
    @14
    wf
    @35
    wph
    cB
    cR
    cB
    @28
    ccrg
    @14
    @8
    cvv
    @11
    evl1addd.b
    @29
    evl1addd.1
    @31
    @33
    pwselbas
    cB
    cB
    @14
    ffn
    syl
    wph
    cB
    cB
    @18
    wf
    @36
    wph
    cB
    cR
    cB
    @28
    ccrg
    @18
    @8
    cvv
    @11
    evl1addd.b
    @29
    evl1addd.1
    @31
    @34
    pwselbas
    cB
    cB
    @18
    ffn
    syl
    @31
    evl1addd.2
    cB
    c.pl
    @14
    @18
    cvv
    cY
    fnfvof
    syl22anc
    wph
    @15
    cV
    @19
    cW
    c.pl
    wph
    @6
    @16
    evl1addd.3
    simprd
    wph
    @7
    @20
    evl1addd.4
    simprd
    oveq12d
    3eqtrd
    jca
end
