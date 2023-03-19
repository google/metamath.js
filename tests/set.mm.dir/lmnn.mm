include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "cfl.mm"
include "caddc.mm"
include "cn0.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "rpreccl.mm"
include "adantl.mm"
include "rpred.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "cxmt.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "wf.mm"
include "eluznn.mm"
include "sylan.mm"
include "ffvelrnd.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "nnrecred.mm"
include "rexrd.mm"
include "rpxr.mm"
include "ad2antlr.mm"
include "adantlr.mm"
include "syldan.mm"
include "adantr.mm"
include "nnred.mm"
include "flltp1.mm"
include "eluzle.mm"
include "ltletrd.mm"
include "wb.mm"
include "simplr.mm"
include "rpregt0.mm"
include "nnrp.mm"
include "rpregt0d.mm"
include "ltrec1.mm"
include "syl2an.mm"
include "mpbid.mm"
include "xrlttrd.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "nnuz.mm"
include "1zzd.mm"
include "eqidd.mm"
include "lmmbrf.mm"
include "mpbir2and.mm"

theorem lmnn
  let wph: wff ph
  let cD: class D
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vx: setvar x
  assume lmnn.2: |- J = ( MetOpen ` D )
  assume lmnn.3: |- ( ph -> D e. ( *Met ` X ) )
  assume lmnn.4: |- ( ph -> P e. X )
  assume lmnn.5: |- ( ph -> F : NN --> X )
  assume lmnn.6: |- ( ( ph /\ k e. NN ) -> ( ( F ` k ) D P ) < ( 1 / k ) )

  disjoint D k
  disjoint F k
  disjoint P k
  disjoint k ph
  disjoint X k
  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint D x
  disjoint F j
  disjoint F x
  disjoint P j
  disjoint P x
  disjoint j ph
  disjoint ph x
  disjoint X j
  disjoint X x
  disjoint J x
  assert |- ( ph -> F ( ~~>t ` J ) P )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cP
    cX
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    cP
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    lmnn.4
    wph
    @9
    vx
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    c1
    @4
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @5
    vk
    @14
    cuz
    cfv
    #
    wral
    #
    @9
    @11
    @13
    cn0
    wcel
    #
    @15
    @11
    @12
    cr
    wcel
    #
    cc0
    @12
    cle
    wbr
    @18
    @11
    @12
    @10
    @12
    crp
    wcel
    wph
    @4
    rpreccl
    adantl
    #
    rpred
    #
    @11
    @12
    @20
    rpge0d
    @12
    flge0nn0
    syl2anc
    @13
    nn0p1nn
    syl
    #
    @11
    @5
    vk
    @16
    @11
    @1
    @16
    wcel
    #
    wa
    #
    @3
    c1
    @1
    cdiv
    co
    #
    @4
    @24
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @2
    cX
    wcel
    @0
    @3
    cxr
    wcel
    wph
    @26
    @10
    @23
    lmnn.3
    ad2antrr
    @24
    cn
    cX
    @1
    cF
    wph
    cn
    cX
    cF
    wf
    @10
    @23
    lmnn.5
    ad2antrr
    @11
    @15
    @23
    @1
    cn
    wcel
    #
    @22
    @1
    @14
    eluznn
    sylan
    #
    ffvelrnd
    wph
    @0
    @10
    @23
    lmnn.4
    ad2antrr
    @2
    cP
    cD
    cX
    xmetcl
    syl3anc
    @24
    @25
    @24
    @1
    @28
    nnrecred
    rexrd
    @10
    @4
    cxr
    wcel
    wph
    @23
    @4
    rpxr
    ad2antlr
    @11
    @23
    @27
    @3
    @25
    clt
    wbr
    #
    @28
    wph
    @27
    @29
    @10
    lmnn.6
    adantlr
    syldan
    @24
    @12
    @1
    clt
    wbr
    #
    @25
    @4
    clt
    wbr
    #
    @24
    @12
    @14
    @1
    @11
    @19
    @23
    @21
    adantr
    #
    @11
    @14
    cr
    wcel
    @23
    @11
    @14
    @22
    nnred
    adantr
    @24
    @1
    @28
    nnred
    @24
    @19
    @12
    @14
    clt
    wbr
    @32
    @12
    flltp1
    syl
    @23
    @14
    @1
    cle
    wbr
    @11
    @14
    @1
    eluzle
    adantl
    ltletrd
    @24
    @10
    @27
    @30
    @31
    wb
    #
    wph
    @10
    @23
    simplr
    @28
    @10
    @4
    cr
    wcel
    cc0
    @4
    clt
    wbr
    wa
    @1
    cr
    wcel
    cc0
    @1
    clt
    wbr
    wa
    @33
    @27
    @4
    rpregt0
    @27
    @1
    @1
    nnrp
    rpregt0d
    @4
    @1
    ltrec1
    syl2an
    syl2anc
    mpbid
    xrlttrd
    ralrimiva
    @8
    @17
    vj
    @14
    cn
    @6
    @14
    wceq
    @5
    vk
    @7
    @16
    @6
    @14
    cuz
    fveq2
    raleqdv
    rspcev
    syl2anc
    ralrimiva
    wph
    vx
    @2
    cD
    cP
    vj
    vk
    cF
    cJ
    c1
    cX
    cn
    lmnn.2
    lmnn.3
    nnuz
    wph
    1zzd
    wph
    @27
    wa
    @2
    eqidd
    lmnn.5
    lmmbrf
    mpbir2and
end
