include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "wb.mm"
include "eqwrd.mm"
include "3adant3.mm"
include "cun.mm"
include "cfz.mm"
include "elfzofz.mm"
include "fzosplit.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "raleqdv.mm"
include "ralunb.mm"
include "syl6bb.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "3simpa.mm"
include "elfzonn0.mm"
include "0nn0.mm"
include "jctil.mm"
include "elfzo0le.mm"
include "breq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "swrdspsleq.mm"
include "bicomd.mm"
include "syl112anc.mm"
include "lencl.mm"
include "3ad2ant1.mm"
include "jca.mm"
include "nn0re.mm"
include "leidd.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "pm5.32da.mm"

theorem 2swrdeqwrdeq
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. Word V /\ S e. Word V /\ I e. ( 0 ..^ ( # ` W ) ) ) -> ( W = S <-> ( ( # ` W ) = ( # ` S ) /\ ( ( W substr <. 0 , I >. ) = ( S substr <. 0 , I >. ) /\ ( W substr <. I , ( # ` W ) >. ) = ( S substr <. I , ( # ` W ) >. ) ) ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cS
    @0
    wcel
    #
    cI
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    cW
    cS
    wceq
    #
    @3
    cS
    chash
    cfv
    #
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    @10
    cS
    cfv
    wceq
    #
    vi
    @4
    wral
    #
    wa
    #
    @9
    cW
    cc0
    cI
    cop
    #
    csubstr
    co
    cS
    @14
    csubstr
    co
    wceq
    #
    cW
    cI
    @3
    cop
    #
    csubstr
    co
    cS
    @16
    csubstr
    co
    wceq
    #
    wa
    #
    wa
    @1
    @2
    @7
    @13
    wb
    @5
    cW
    vi
    cV
    cS
    eqwrd
    3adant3
    @6
    @9
    @12
    @18
    @6
    @9
    wa
    #
    @12
    @11
    vi
    cc0
    cI
    cfzo
    co
    #
    wral
    #
    @11
    vi
    cI
    @3
    cfzo
    co
    #
    wral
    #
    wa
    #
    @18
    @19
    @12
    @11
    vi
    @20
    @22
    cun
    #
    wral
    @24
    @19
    @11
    vi
    @4
    @25
    @6
    @4
    @25
    wceq
    #
    @9
    @5
    @1
    @26
    @2
    @5
    cI
    cc0
    @3
    cfz
    co
    wcel
    @26
    cI
    cc0
    @3
    elfzofz
    cc0
    @3
    cI
    fzosplit
    syl
    3ad2ant3
    adantr
    raleqdv
    @11
    vi
    @20
    @22
    ralunb
    syl6bb
    @19
    @21
    @15
    @23
    @17
    @19
    @1
    @2
    wa
    #
    cc0
    cn0
    wcel
    #
    cI
    cn0
    wcel
    #
    wa
    #
    cI
    @3
    cle
    wbr
    #
    cI
    @8
    cle
    wbr
    #
    @21
    @15
    wb
    @6
    @27
    @9
    @1
    @2
    @5
    3simpa
    adantr
    #
    @19
    @29
    @28
    @6
    @29
    @9
    @5
    @1
    @29
    @2
    cI
    @3
    elfzonn0
    3ad2ant3
    #
    adantr
    0nn0
    jctil
    @6
    @31
    @9
    @5
    @1
    @31
    @2
    cI
    @3
    elfzo0le
    3ad2ant3
    adantr
    #
    @19
    @31
    @32
    @35
    @9
    @31
    @32
    wb
    @6
    @3
    @8
    cI
    cle
    breq2
    adantl
    mpbid
    @27
    @30
    @31
    @32
    wa
    w3a
    @15
    @21
    cS
    vi
    cc0
    cI
    cV
    cW
    swrdspsleq
    bicomd
    syl112anc
    @19
    @27
    @29
    @3
    cn0
    wcel
    #
    wa
    #
    @3
    @3
    cle
    wbr
    #
    @3
    @8
    cle
    wbr
    #
    @23
    @17
    wb
    @33
    @6
    @37
    @9
    @6
    @29
    @36
    @34
    @1
    @2
    @36
    @5
    cV
    cW
    lencl
    #
    3ad2ant1
    jca
    adantr
    @6
    @38
    @9
    @1
    @2
    @38
    @5
    @1
    @36
    @38
    @40
    @36
    @3
    @3
    nn0re
    leidd
    syl
    3ad2ant1
    adantr
    #
    @19
    @38
    @39
    @41
    @9
    @38
    @39
    wb
    @6
    @3
    @8
    @3
    cle
    breq2
    adantl
    mpbid
    @27
    @37
    @38
    @39
    wa
    w3a
    @17
    @23
    cS
    vi
    cI
    @3
    cV
    cW
    swrdspsleq
    bicomd
    syl112anc
    anbi12d
    bitrd
    pm5.32da
    bitrd
end
