include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "csupp.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "wne.mm"
include "wfn.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "cmap.mm"
include "elmapfn.mm"
include "syl.mm"
include "nn0ex.mm"
include "a1i.mm"
include "3jca.mm"
include "adantr.mm"
include "elsuppfn.mm"
include "breq2.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "wn.mm"
include "cle.mm"
include "simplr.mm"
include "cr.mm"
include "nn0re.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "biimpar.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "a1d.mm"
include "ex.mm"
include "eqneqall.mm"
include "jad.mm"
include "com23.mm"
include "com14.mm"
include "pm2.43a.mm"
include "imp.mm"
include "com13.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "mpdan.mm"

theorem suppssfz
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cF: class F
  let cV: class V
  let cZ: class Z
  let vn: setvar n
  assume suppssfz.z: |- ( ph -> Z e. V )
  assume suppssfz.f: |- ( ph -> F e. ( B ^m NN0 ) )
  assume suppssfz.s: |- ( ph -> S e. NN0 )
  assume suppssfz.b: |- ( ph -> A. x e. NN0 ( S < x -> ( F ` x ) = Z ) )

  disjoint F x
  disjoint S x
  disjoint Z x
  disjoint F n
  disjoint n x
  disjoint S n
  disjoint Z n
  disjoint n ph
  assert |- ( ph -> ( F supp Z ) C_ ( 0 ... S ) )

  proof
    wph
    cS
    vx
    cv
    #
    clt
    wbr
    #
    @0
    cF
    cfv
    #
    cZ
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    cF
    cZ
    csupp
    co
    #
    cc0
    cS
    cfz
    co
    #
    wss
    suppssfz.b
    wph
    @5
    wa
    #
    vn
    @6
    @7
    @8
    vn
    cv
    #
    @6
    wcel
    #
    @9
    cn0
    wcel
    #
    @9
    cF
    cfv
    #
    cZ
    wne
    #
    wa
    #
    @9
    @7
    wcel
    #
    @8
    cF
    cn0
    wfn
    #
    cn0
    cvv
    wcel
    #
    cZ
    cV
    wcel
    #
    w3a
    #
    @10
    @14
    wb
    wph
    @19
    @5
    wph
    @16
    @17
    @18
    wph
    cF
    cB
    cn0
    cmap
    co
    wcel
    @16
    suppssfz.f
    cF
    cB
    cn0
    elmapfn
    syl
    @17
    wph
    nn0ex
    a1i
    suppssfz.z
    3jca
    adantr
    @9
    cF
    cvv
    cV
    cn0
    cZ
    elsuppfn
    syl
    wph
    @5
    @14
    @15
    wi
    @14
    @5
    wph
    @15
    @11
    @13
    @5
    wph
    @15
    wi
    #
    wi
    @11
    @5
    @13
    @20
    @5
    @11
    @13
    @20
    wi
    #
    @11
    @5
    @11
    @21
    wi
    #
    @11
    @5
    wa
    cS
    @9
    clt
    wbr
    #
    @12
    cZ
    wceq
    #
    wi
    #
    @22
    @4
    @25
    vx
    @9
    cn0
    @0
    @9
    wceq
    #
    @1
    @23
    @3
    @24
    @0
    @9
    cS
    clt
    breq2
    @26
    @2
    @12
    cZ
    @0
    @9
    cF
    fveq2
    eqeq1d
    imbi12d
    rspcva
    wph
    @11
    @13
    @25
    @15
    wph
    @11
    @13
    @25
    @15
    wi
    wi
    wph
    @11
    wa
    #
    @25
    @13
    @15
    @27
    @23
    @24
    @13
    @15
    wi
    #
    @27
    @23
    wn
    #
    @28
    @27
    @29
    wa
    #
    @15
    @13
    @30
    @11
    cS
    cn0
    wcel
    #
    @9
    cS
    cle
    wbr
    #
    @15
    wph
    @11
    @29
    simplr
    @27
    @31
    @29
    wph
    @31
    @11
    suppssfz.s
    adantr
    adantr
    @27
    @32
    @29
    @11
    @9
    cr
    wcel
    cS
    cr
    wcel
    #
    @32
    @29
    wb
    wph
    @9
    nn0re
    wph
    @31
    @33
    suppssfz.s
    cS
    nn0re
    syl
    @9
    cS
    lenlt
    syl2anr
    biimpar
    @9
    cS
    elfz2nn0
    syl3anbrc
    a1d
    ex
    @24
    @28
    wi
    @27
    @15
    @12
    cZ
    eqneqall
    a1i
    jad
    com23
    ex
    com14
    syl
    ex
    pm2.43a
    com23
    imp
    com13
    imp
    sylbid
    ssrdv
    mpdan
end
