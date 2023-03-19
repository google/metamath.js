include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "crrv.mm"
include "cv.mm"
include "wi.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "cz.mm"
include "1z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "1nn.mm"
include "ffvelrnda.mm"
include "mpan2.mm"
include "syl5eqel.mm"
include "cuz.mm"
include "seqp1.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "ad2antlr.mm"
include "cprb.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "peano2nn.mm"
include "sylan2.mm"
include "adantr.mm"
include "rrvadd.mm"
include "eqeltrd.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem rrvsum
  let wph: wff ph
  let cP: class P
  let cS: class S
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vn: setvar n
  assume rrvsum.1: |- ( ph -> P e. Prob )
  assume rrvsum.2: |- ( ph -> X : NN --> ( rRndVar ` P ) )
  assume rrvsum.3: |- ( ( ph /\ N e. NN ) -> S = ( seq 1 ( oF + , X ) ` N ) )


  assert |- ( ( ph /\ N e. NN ) -> S e. ( rRndVar ` P ) )

  proof
    wph
    cN
    cn
    wcel
    #
    wa
    cS
    cN
    caddc
    cof
    #
    cX
    c1
    cseq
    #
    cfv
    #
    cP
    crrv
    cfv
    #
    rrvsum.3
    @0
    wph
    @3
    @4
    wcel
    #
    wph
    vk
    cv
    #
    @2
    cfv
    #
    @4
    wcel
    #
    wi
    wph
    c1
    @2
    cfv
    #
    @4
    wcel
    #
    wi
    wph
    vn
    cv
    #
    @2
    cfv
    #
    @4
    wcel
    #
    wi
    wph
    @11
    c1
    caddc
    co
    #
    @2
    cfv
    #
    @4
    wcel
    #
    wi
    wph
    @5
    wi
    vk
    vn
    cN
    @6
    c1
    wceq
    #
    @8
    @10
    wph
    @17
    @7
    @9
    @4
    @6
    c1
    @2
    fveq2
    eleq1d
    imbi2d
    @6
    @11
    wceq
    #
    @8
    @13
    wph
    @18
    @7
    @12
    @4
    @6
    @11
    @2
    fveq2
    eleq1d
    imbi2d
    @6
    @14
    wceq
    #
    @8
    @16
    wph
    @19
    @7
    @15
    @4
    @6
    @14
    @2
    fveq2
    eleq1d
    imbi2d
    @6
    cN
    wceq
    #
    @8
    @5
    wph
    @20
    @7
    @3
    @4
    @6
    cN
    @2
    fveq2
    eleq1d
    imbi2d
    wph
    @9
    c1
    cX
    cfv
    #
    @4
    c1
    cz
    wcel
    @9
    @21
    wceq
    1z
    @1
    cX
    c1
    seq1
    ax-mp
    wph
    c1
    cn
    wcel
    @21
    @4
    wcel
    1nn
    wph
    cn
    @4
    c1
    cX
    rrvsum.2
    ffvelrnda
    mpan2
    syl5eqel
    @11
    cn
    wcel
    #
    wph
    @13
    @16
    wph
    @22
    @13
    @16
    wi
    wph
    @22
    wa
    #
    @13
    @16
    @23
    @13
    wa
    #
    @15
    @12
    @14
    cX
    cfv
    #
    @1
    co
    #
    @4
    @22
    @15
    @26
    wceq
    #
    wph
    @13
    @27
    @11
    c1
    cuz
    cfv
    cn
    @1
    cX
    c1
    @11
    seqp1
    nnuz
    eleq2s
    ad2antlr
    @24
    cP
    @12
    @25
    wph
    cP
    cprb
    wcel
    @22
    @13
    rrvsum.1
    ad2antrr
    @23
    @13
    simpr
    @23
    @25
    @4
    wcel
    #
    @13
    @22
    wph
    @14
    cn
    wcel
    @28
    @11
    peano2nn
    wph
    cn
    @4
    @14
    cX
    rrvsum.2
    ffvelrnda
    sylan2
    adantr
    rrvadd
    eqeltrd
    ex
    expcom
    a2d
    nnind
    impcom
    eqeltrd
end
