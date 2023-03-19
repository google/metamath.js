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
include "cpfx.mm"
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
include "eqidd.mm"
include "biantrurd.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "3simpa.mm"
include "elfzonn0.mm"
include "jca.mm"
include "elfzo0le.mm"
include "breq2.mm"
include "eqcoms.mm"
include "adantl.mm"
include "mpbird.mm"
include "pfxeq.mm"
include "syl112anc.mm"
include "bitr4d.mm"
include "lencl.mm"
include "anim12i.mm"
include "3adant2.mm"
include "ancomd.mm"
include "nn0red.mm"
include "leidd.mm"
include "3ad2ant1.mm"
include "cr.mm"
include "eqle.mm"
include "sylan.mm"
include "swrdspsleq.mm"
include "bicomd.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "pm5.32da.mm"

theorem pfxsuffeqwrdeq
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ S e. Word V /\ I e. ( 0 ..^ ( # ` W ) ) ) -> ( W = S <-> ( ( # ` W ) = ( # ` S ) /\ ( ( W prefix I ) = ( S prefix I ) /\ ( W substr <. I , ( # ` W ) >. ) = ( S substr <. I , ( # ` W ) >. ) ) ) ) )

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
    cI
    cpfx
    co
    cS
    cI
    cpfx
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
    @15
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
    @17
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
    @17
    @18
    @12
    @11
    vi
    @19
    @21
    cun
    #
    wral
    @23
    @18
    @11
    vi
    @4
    @24
    @6
    @4
    @24
    wceq
    #
    @9
    @5
    @1
    @25
    @2
    @5
    cI
    cc0
    @3
    cfz
    co
    wcel
    @25
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
    @19
    @21
    ralunb
    syl6bb
    @18
    @20
    @14
    @22
    @16
    @18
    @20
    cI
    cI
    wceq
    #
    @20
    wa
    #
    @14
    @18
    @26
    @20
    @18
    cI
    eqidd
    biantrurd
    @18
    @1
    @2
    wa
    #
    cI
    cn0
    wcel
    #
    @29
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
    @14
    @27
    wb
    @6
    @28
    @9
    @1
    @2
    @5
    3simpa
    adantr
    #
    @6
    @30
    @9
    @5
    @1
    @30
    @2
    @5
    @29
    @29
    cI
    @3
    elfzonn0
    #
    @34
    jca
    3ad2ant3
    adantr
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
    @18
    @32
    @31
    @35
    @9
    @32
    @31
    wb
    #
    @6
    @36
    @8
    @3
    @8
    @3
    cI
    cle
    breq2
    eqcoms
    adantl
    mpbird
    cS
    vi
    cI
    cI
    cV
    cW
    pfxeq
    syl112anc
    bitr4d
    @18
    @28
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
    @22
    @16
    wb
    @33
    @6
    @38
    @9
    @6
    @37
    @29
    @1
    @5
    @37
    @29
    wa
    @2
    @1
    @37
    @5
    @29
    cV
    cW
    lencl
    #
    @34
    anim12i
    3adant2
    ancomd
    adantr
    @6
    @39
    @9
    @1
    @2
    @39
    @5
    @1
    @3
    @1
    @3
    @41
    nn0red
    #
    leidd
    3ad2ant1
    adantr
    @6
    @3
    cr
    wcel
    #
    @9
    @40
    @1
    @2
    @43
    @5
    @42
    3ad2ant1
    @3
    @8
    eqle
    sylan
    @28
    @38
    @39
    @40
    wa
    w3a
    @16
    @22
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
