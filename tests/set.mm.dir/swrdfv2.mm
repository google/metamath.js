include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cfzo.mm"
include "co.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "caddc.mm"
include "cc0.mm"
include "cfz.mm"
include "wceq.mm"
include "simp1.mm"
include "simpl.mm"
include "eluznn0.mm"
include "eluzle.mm"
include "adantl.mm"
include "3jca.mm"
include "3ad2ant2.mm"
include "elfz2nn0.mm"
include "sylibr.mm"
include "anim1i.mm"
include "3adant1.mm"
include "wb.mm"
include "lencl.mm"
include "3ad2ant1.mm"
include "fznn0.mm"
include "syl.mm"
include "mpbird.mm"
include "adantr.mm"
include "cz.mm"
include "cc.mm"
include "nn0cn.mm"
include "eluzelcn.mm"
include "pncan3.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "eluzelz.mm"
include "nn0z.mm"
include "zsubcld.mm"
include "fzosubel3.mm"
include "syl2anc.mm"
include "swrdfv.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "npcan.mm"
include "syl2anr.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem swrdfv2
  let cS: class S
  let cF: class F
  let cL: class L
  let cV: class V
  let cX: class X


  assert |- ( ( ( S e. Word V /\ ( F e. NN0 /\ L e. ( ZZ>= ` F ) ) /\ L <_ ( # ` S ) ) /\ X e. ( F ..^ L ) ) -> ( ( S substr <. F , L >. ) ` ( X - F ) ) = ( S ` X ) )

  proof
    cS
    cV
    cword
    wcel
    #
    cF
    cn0
    wcel
    #
    cL
    cF
    cuz
    cfv
    wcel
    #
    wa
    #
    cL
    cS
    chash
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    cX
    cF
    cL
    cfzo
    co
    #
    wcel
    #
    wa
    #
    cX
    cF
    cmin
    co
    #
    cS
    cF
    cL
    cop
    csubstr
    co
    cfv
    #
    @10
    cF
    caddc
    co
    #
    cS
    cfv
    #
    cX
    cS
    cfv
    @9
    @0
    cF
    cc0
    cL
    cfz
    co
    wcel
    #
    cL
    cc0
    @4
    cfz
    co
    wcel
    #
    w3a
    #
    @10
    cc0
    cL
    cF
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    @11
    @13
    wceq
    @6
    @16
    @8
    @6
    @0
    @14
    @15
    @0
    @3
    @5
    simp1
    @6
    @1
    cL
    cn0
    wcel
    #
    cF
    cL
    cle
    wbr
    #
    w3a
    #
    @14
    @3
    @0
    @21
    @5
    @3
    @1
    @19
    @20
    @1
    @2
    simpl
    cL
    cF
    eluznn0
    #
    @2
    @20
    @1
    cF
    cL
    eluzle
    adantl
    3jca
    3ad2ant2
    cF
    cL
    elfz2nn0
    sylibr
    @6
    @15
    @19
    @5
    wa
    #
    @3
    @5
    @23
    @0
    @3
    @19
    @5
    @22
    anim1i
    3adant1
    @6
    @4
    cn0
    wcel
    #
    @15
    @23
    wb
    @0
    @3
    @24
    @5
    cV
    cS
    lencl
    3ad2ant1
    cL
    @4
    fznn0
    syl
    mpbird
    3jca
    adantr
    @9
    cX
    cF
    cF
    @17
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @17
    cz
    wcel
    #
    @18
    @6
    @8
    @27
    @6
    @7
    @26
    cX
    @6
    cL
    @25
    cF
    cfzo
    @3
    @0
    cL
    @25
    wceq
    @5
    @3
    @25
    cL
    @1
    cF
    cc
    wcel
    #
    cL
    cc
    wcel
    @25
    cL
    wceq
    @2
    cF
    nn0cn
    #
    cF
    cL
    eluzelcn
    cF
    cL
    pncan3
    syl2an
    eqcomd
    3ad2ant2
    oveq2d
    eleq2d
    biimpa
    @6
    @28
    @8
    @3
    @0
    @28
    @5
    @3
    cL
    cF
    @2
    cL
    cz
    wcel
    @1
    cF
    cL
    eluzelz
    adantl
    @1
    cF
    cz
    wcel
    @2
    cF
    nn0z
    adantr
    zsubcld
    3ad2ant2
    adantr
    cX
    cF
    @17
    fzosubel3
    syl2anc
    cV
    cS
    cF
    cL
    @10
    swrdfv
    syl2anc
    @9
    @12
    cX
    cS
    @8
    cX
    cc
    wcel
    @29
    @12
    cX
    wceq
    @6
    @8
    cX
    cX
    cF
    cL
    elfzoelz
    zcnd
    @3
    @0
    @29
    @5
    @1
    @29
    @2
    @30
    adantr
    3ad2ant2
    cX
    cF
    npcan
    syl2anr
    fveq2d
    eqtrd
end
