include "cfv.mm"
include "c0g.mm"
include "co.mm"
include "cle.mm"
include "cgrp.mm"
include "wcel.mm"
include "wceq.mm"
include "cngp.mm"
include "ngpgrp.mm"
include "syl.mm"
include "ctopon.mm"
include "clm.mm"
include "wbr.mm"
include "cxmt.mm"
include "cxme.mm"
include "cmt.mm"
include "ngpms.mm"
include "msxms.mm"
include "xmsxmet.mm"
include "mopntopon.mm"
include "lmcl.mm"
include "syl2anc.mm"
include "cds.mm"
include "eqid.mm"
include "nmval2.mm"
include "grpidcl.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "c1.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cv.mm"
include "wa.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "eqbrtrrd.mm"
include "lmle.mm"
include "eqbrtrd.mm"

theorem nglmle
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cJ: class J
  let cN: class N
  let cX: class X
  assume nglmle.1: |- X = ( Base ` G )
  assume nglmle.2: |- D = ( ( dist ` G ) |` ( X X. X ) )
  assume nglmle.3: |- J = ( MetOpen ` D )
  assume nglmle.5: |- N = ( norm ` G )
  assume nglmle.6: |- ( ph -> G e. NrmGrp )
  assume nglmle.7: |- ( ph -> F : NN --> X )
  assume nglmle.8: |- ( ph -> F ( ~~>t ` J ) P )
  assume nglmle.9: |- ( ph -> R e. RR* )
  assume nglmle.10: |- ( ( ph /\ k e. NN ) -> ( N ` ( F ` k ) ) <_ R )

  disjoint F k
  disjoint D k
  disjoint G k
  disjoint J k
  disjoint P k
  disjoint R k
  disjoint X k
  disjoint k ph
  assert |- ( ph -> ( N ` P ) <_ R )

  proof
    wph
    cP
    cN
    cfv
    #
    cG
    c0g
    cfv
    #
    cP
    cD
    co
    #
    cR
    cle
    wph
    @0
    cP
    @1
    cD
    co
    #
    @2
    wph
    cG
    cgrp
    wcel
    #
    cP
    cX
    wcel
    #
    @0
    @3
    wceq
    wph
    cG
    cngp
    wcel
    #
    @4
    nglmle.6
    cG
    ngpgrp
    syl
    #
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cP
    cJ
    clm
    cfv
    wbr
    @5
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @8
    wph
    cG
    cxme
    wcel
    #
    @9
    wph
    cG
    cmt
    wcel
    #
    @10
    wph
    @6
    @11
    nglmle.6
    cG
    ngpms
    syl
    cG
    msxms
    syl
    cD
    cG
    cX
    nglmle.1
    nglmle.2
    xmsxmet
    syl
    #
    cD
    cJ
    cX
    nglmle.3
    mopntopon
    syl
    nglmle.8
    cP
    cF
    cJ
    cX
    lmcl
    syl2anc
    #
    cP
    cG
    cds
    cfv
    #
    cD
    cN
    cG
    cX
    @1
    nglmle.5
    nglmle.1
    @1
    eqid
    #
    @14
    eqid
    #
    nglmle.2
    nmval2
    syl2anc
    wph
    @9
    @5
    @1
    cX
    wcel
    #
    @3
    @2
    wceq
    @12
    @13
    wph
    @4
    @17
    @7
    cX
    cG
    @1
    nglmle.1
    @15
    grpidcl
    syl
    #
    cP
    @1
    cD
    cX
    xmetsym
    syl3anc
    eqtrd
    wph
    cD
    cP
    @1
    cR
    vk
    cF
    cJ
    c1
    cX
    cn
    nnuz
    nglmle.3
    @12
    wph
    1zzd
    nglmle.8
    @18
    nglmle.9
    wph
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    @19
    cF
    cfv
    #
    cN
    cfv
    #
    @1
    @22
    cD
    co
    #
    cR
    cle
    @21
    @23
    @22
    @1
    cD
    co
    #
    @24
    @21
    @4
    @22
    cX
    wcel
    #
    @23
    @25
    wceq
    wph
    @4
    @20
    @7
    adantr
    wph
    cn
    cX
    @19
    cF
    nglmle.7
    ffvelrnda
    #
    @22
    @14
    cD
    cN
    cG
    cX
    @1
    nglmle.5
    nglmle.1
    @15
    @16
    nglmle.2
    nmval2
    syl2anc
    @21
    @9
    @26
    @17
    @25
    @24
    wceq
    wph
    @9
    @20
    @12
    adantr
    @27
    wph
    @17
    @20
    @18
    adantr
    @22
    @1
    cD
    cX
    xmetsym
    syl3anc
    eqtrd
    nglmle.10
    eqbrtrrd
    lmle
    eqbrtrd
end
