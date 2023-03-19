include "cle.mm"
include "wbr.mm"
include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "wceq.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpl.mm"
include "swrdsb0eq.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "wn.mm"
include "wi.mm"
include "cr.mm"
include "nn0re.mm"
include "clt.mm"
include "ltnle.mm"
include "ltle.mm"
include "sylbird.mm"
include "syl2an.mm"
include "3ad2ant2.mm"
include "cmin.mm"
include "cuz.mm"
include "simpl1l.mm"
include "simpl2l.mm"
include "cz.mm"
include "nn0z.mm"
include "anim12i.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "eluz2.mm"
include "simpl3l.mm"
include "swrdlen2.mm"
include "syl121anc.mm"
include "simpl1r.mm"
include "simpl3r.mm"
include "eqtr4d.mm"
include "ex.mm"
include "syld.mm"
include "impcom.mm"
include "pm2.61ian.mm"

theorem swrdsbslen
  let cU: class U
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( ( W e. Word V /\ U e. Word V ) /\ ( M e. NN0 /\ N e. NN0 ) /\ ( N <_ ( # ` W ) /\ N <_ ( # ` U ) ) ) -> ( # ` ( W substr <. M , N >. ) ) = ( # ` ( U substr <. M , N >. ) ) )

  proof
    cN
    cM
    cle
    wbr
    #
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @1
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
    cN
    cW
    chash
    cfv
    cle
    wbr
    #
    cN
    cU
    chash
    cfv
    cle
    wbr
    #
    wa
    #
    w3a
    #
    cW
    cM
    cN
    cop
    #
    csubstr
    co
    #
    chash
    cfv
    #
    cU
    @12
    csubstr
    co
    #
    chash
    cfv
    #
    wceq
    #
    @0
    @11
    wa
    #
    @13
    @15
    chash
    @18
    @4
    @7
    @0
    @13
    @15
    wceq
    @0
    @4
    @7
    @10
    simpr1
    @0
    @4
    @7
    @10
    simpr2
    @0
    @11
    simpl
    cU
    cM
    cN
    cV
    cW
    swrdsb0eq
    syl3anc
    fveq2d
    @11
    @0
    wn
    #
    @17
    @11
    @19
    cM
    cN
    cle
    wbr
    #
    @17
    @7
    @4
    @19
    @20
    wi
    #
    @10
    @5
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @21
    @6
    cM
    nn0re
    cN
    nn0re
    @22
    @23
    wa
    @19
    cM
    cN
    clt
    wbr
    @20
    cM
    cN
    ltnle
    cM
    cN
    ltle
    sylbird
    syl2an
    3ad2ant2
    @11
    @20
    @17
    @11
    @20
    wa
    #
    @14
    cN
    cM
    cmin
    co
    #
    @16
    @24
    @2
    @5
    cN
    cM
    cuz
    cfv
    wcel
    #
    @8
    @14
    @25
    wceq
    @2
    @3
    @7
    @10
    @20
    simpl1l
    @5
    @6
    @4
    @10
    @20
    simpl2l
    #
    @24
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @20
    w3a
    #
    @26
    @24
    @28
    @29
    wa
    #
    @20
    wa
    @30
    @11
    @31
    @20
    @7
    @4
    @31
    @10
    @5
    @28
    @6
    @29
    cM
    nn0z
    cN
    nn0z
    anim12i
    3ad2ant2
    anim1i
    @28
    @29
    @20
    df-3an
    sylibr
    cM
    cN
    eluz2
    sylibr
    #
    @8
    @9
    @4
    @7
    @20
    simpl3l
    cW
    cM
    cN
    cV
    swrdlen2
    syl121anc
    @24
    @3
    @5
    @26
    @9
    @16
    @25
    wceq
    @2
    @3
    @7
    @10
    @20
    simpl1r
    @27
    @32
    @8
    @9
    @4
    @7
    @20
    simpl3r
    cU
    cM
    cN
    cV
    swrdlen2
    syl121anc
    eqtr4d
    ex
    syld
    impcom
    pm2.61ian
end
