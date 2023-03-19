include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cpfx.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "wb.mm"
include "pfxcl.mm"
include "anim12i.mm"
include "3ad2ant1.mm"
include "eqwrd.mm"
include "syl.mm"
include "cfz.mm"
include "simpl.mm"
include "3ad2ant2.mm"
include "lencl.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "pfxlen.mm"
include "syl2anc.mm"
include "simpr.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "anbi1d.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "pfxfv.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "3bitrd.mm"

theorem pfxeq
  let cU: class U
  let vi: setvar i
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x

  disjoint M i
  disjoint N i
  disjoint U i
  disjoint V i
  disjoint W i
  disjoint k x
  assert |- ( ( ( W e. Word V /\ U e. Word V ) /\ ( M e. NN0 /\ N e. NN0 ) /\ ( M <_ ( # ` W ) /\ N <_ ( # ` U ) ) ) -> ( ( W prefix M ) = ( U prefix N ) <-> ( M = N /\ A. i e. ( 0 ..^ M ) ( W ` i ) = ( U ` i ) ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @0
    wcel
    #
    wa
    #
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cM
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    cN
    cU
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    w3a
    #
    cW
    cM
    cpfx
    co
    #
    cU
    cN
    cpfx
    co
    #
    wceq
    #
    @13
    chash
    cfv
    #
    @14
    chash
    cfv
    #
    wceq
    #
    vi
    cv
    #
    @13
    cfv
    #
    @19
    @14
    cfv
    #
    wceq
    #
    vi
    cc0
    @16
    cfzo
    co
    #
    wral
    #
    wa
    #
    cM
    cN
    wceq
    #
    @24
    wa
    @26
    @19
    cW
    cfv
    #
    @19
    cU
    cfv
    #
    wceq
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    wa
    @12
    @13
    @0
    wcel
    #
    @14
    @0
    wcel
    #
    wa
    #
    @15
    @25
    wb
    @3
    @6
    @34
    @11
    @1
    @32
    @2
    @33
    cV
    cW
    cM
    pfxcl
    cV
    cU
    cN
    pfxcl
    anim12i
    3ad2ant1
    @13
    vi
    cV
    @14
    eqwrd
    syl
    @12
    @18
    @26
    @24
    @12
    @16
    cM
    @17
    cN
    @12
    @1
    cM
    cc0
    @7
    cfz
    co
    wcel
    #
    @16
    cM
    wceq
    #
    @3
    @6
    @1
    @11
    @1
    @2
    simpl
    3ad2ant1
    #
    @12
    @4
    @7
    cn0
    wcel
    #
    @8
    @35
    @6
    @3
    @4
    @11
    @4
    @5
    simpl
    3ad2ant2
    @3
    @6
    @38
    @11
    @1
    @38
    @2
    cV
    cW
    lencl
    adantr
    3ad2ant1
    @11
    @3
    @8
    @6
    @8
    @10
    simpl
    3ad2ant3
    cM
    @7
    elfz2nn0
    syl3anbrc
    #
    cV
    cW
    cM
    pfxlen
    #
    syl2anc
    @12
    @2
    cN
    cc0
    @9
    cfz
    co
    wcel
    #
    @17
    cN
    wceq
    @3
    @6
    @2
    @11
    @1
    @2
    simpr
    3ad2ant1
    #
    @12
    @5
    @9
    cn0
    wcel
    #
    @10
    @41
    @6
    @3
    @5
    @11
    @4
    @5
    simpr
    3ad2ant2
    @3
    @6
    @43
    @11
    @2
    @43
    @1
    cV
    cU
    lencl
    adantl
    3ad2ant1
    @11
    @3
    @10
    @6
    @8
    @10
    simpr
    3ad2ant3
    cN
    @9
    elfz2nn0
    syl3anbrc
    #
    cV
    cU
    cN
    pfxlen
    syl2anc
    eqeq12d
    anbi1d
    @12
    @26
    @24
    @31
    @12
    @26
    wa
    #
    @24
    @22
    vi
    @30
    wral
    @31
    @45
    @22
    vi
    @23
    @30
    @45
    @16
    cM
    cc0
    cfzo
    @45
    @1
    @35
    @36
    @12
    @1
    @26
    @37
    adantr
    #
    @12
    @35
    @26
    @39
    adantr
    #
    @40
    syl2anc
    oveq2d
    raleqdv
    @45
    @22
    @29
    vi
    @30
    @45
    @19
    @30
    wcel
    #
    wa
    #
    @20
    @27
    @21
    @28
    @49
    @1
    @35
    @48
    @20
    @27
    wceq
    @45
    @1
    @48
    @46
    adantr
    @45
    @35
    @48
    @47
    adantr
    @45
    @48
    simpr
    @19
    cM
    cV
    cW
    pfxfv
    syl3anc
    @49
    @2
    @41
    @19
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    @21
    @28
    wceq
    @12
    @2
    @26
    @48
    @42
    ad2antrr
    @12
    @41
    @26
    @48
    @44
    ad2antrr
    @45
    @48
    @51
    @26
    @48
    @51
    wb
    @12
    @26
    @30
    @50
    @19
    cM
    cN
    cc0
    cfzo
    oveq2
    eleq2d
    adantl
    biimpa
    @19
    cN
    cV
    cU
    pfxfv
    syl3anc
    eqeq12d
    ralbidva
    bitrd
    pm5.32da
    3bitrd
end
