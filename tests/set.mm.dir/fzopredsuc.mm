include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "cun.mm"
include "wi.mm"
include "cz.mm"
include "wa.mm"
include "unidm.mm"
include "eqcomi.mm"
include "oveq1.mm"
include "fzsn.mm"
include "sylan9eqr.mm"
include "sneq.mm"
include "oveq1d.mm"
include "uneq12d.mm"
include "uneq1d.mm"
include "c0.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "zre.mm"
include "lep1d.mm"
include "peano2z.mm"
include "zred.mm"
include "lenltd.mm"
include "mpbid.mm"
include "wb.mm"
include "fzonlt0.mm"
include "mpancom.mm"
include "uneq2d.mm"
include "un0.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "ex.mm"
include "eluzelz.mm"
include "syl11.mm"
include "fzisfzounsn.mm"
include "adantl.mm"
include "w3a.mm"
include "eluz2.mm"
include "simpl1.mm"
include "simpl2.mm"
include "wne.mm"
include "nesym.mm"
include "cr.mm"
include "ltlen.mm"
include "syl2an.mm"
include "biimprd.mm"
include "exp4b.mm"
include "3imp.mm"
include "syl5bir.mm"
include "imp.mm"
include "3jca.mm"
include "sylbi.mm"
include "impcom.mm"
include "fzopred.mm"
include "syl.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem fzopredsuc
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` M ) -> ( M ... N ) = ( ( { M } u. ( ( M + 1 ) ..^ N ) ) u. { N } ) )

  proof
    cM
    cN
    wceq
    #
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cN
    cfz
    co
    #
    cM
    csn
    #
    cM
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    #
    cun
    #
    cN
    csn
    #
    cun
    #
    wceq
    #
    wi
    cN
    cz
    wcel
    #
    @0
    @9
    @1
    @10
    @0
    @9
    @10
    @0
    wa
    @7
    @7
    @7
    cun
    #
    @2
    @8
    @11
    @7
    @7
    unidm
    eqcomi
    @0
    @10
    @2
    cN
    cN
    cfz
    co
    @7
    cM
    cN
    cN
    cfz
    oveq1
    cN
    fzsn
    sylan9eqr
    @0
    @10
    @8
    @7
    cN
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    #
    cun
    #
    @7
    cun
    @11
    @0
    @6
    @14
    @7
    @0
    @3
    @7
    @5
    @13
    cM
    cN
    sneq
    @0
    @4
    @12
    cN
    cfzo
    cM
    cN
    c1
    caddc
    oveq1
    oveq1d
    uneq12d
    uneq1d
    @10
    @14
    @7
    @7
    @10
    @14
    @7
    c0
    cun
    @7
    @10
    @13
    c0
    @7
    @10
    @12
    cN
    clt
    wbr
    wn
    #
    @13
    c0
    wceq
    #
    @10
    cN
    @12
    cle
    wbr
    @15
    @10
    cN
    cN
    zre
    #
    lep1d
    @10
    cN
    @12
    @17
    @10
    @12
    cN
    peano2z
    #
    zred
    lenltd
    mpbid
    @12
    cz
    wcel
    @10
    @15
    @16
    wb
    @18
    @12
    cN
    fzonlt0
    mpancom
    mpbid
    uneq2d
    @7
    un0
    syl6eq
    uneq1d
    sylan9eqr
    3eqtr4a
    ex
    cM
    cN
    eluzelz
    syl11
    @0
    wn
    #
    @1
    @9
    @19
    @1
    wa
    #
    @2
    cM
    cN
    cfzo
    co
    #
    @7
    cun
    #
    @8
    @1
    @2
    @22
    wceq
    @19
    cM
    cN
    fzisfzounsn
    adantl
    @20
    @21
    @6
    @7
    @20
    cM
    cz
    wcel
    #
    @10
    cM
    cN
    clt
    wbr
    #
    w3a
    #
    @21
    @6
    wceq
    @1
    @19
    @25
    @1
    @23
    @10
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    @19
    @25
    wi
    cM
    cN
    eluz2
    @27
    @19
    @25
    @27
    @19
    wa
    @23
    @10
    @24
    @23
    @10
    @26
    @19
    simpl1
    @23
    @10
    @26
    @19
    simpl2
    @27
    @19
    @24
    @19
    cN
    cM
    wne
    #
    @27
    @24
    cN
    cM
    nesym
    @23
    @10
    @26
    @28
    @24
    wi
    @23
    @10
    @26
    @28
    @24
    @23
    @10
    wa
    @24
    @26
    @28
    wa
    #
    @23
    cM
    cr
    wcel
    cN
    cr
    wcel
    @24
    @29
    wb
    @10
    cM
    zre
    @17
    cM
    cN
    ltlen
    syl2an
    biimprd
    exp4b
    3imp
    syl5bir
    imp
    3jca
    ex
    sylbi
    impcom
    cM
    cN
    fzopred
    syl
    uneq1d
    eqtrd
    ex
    pm2.61i
end
