include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "elnn0.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "cr.mm"
include "nnre.mm"
include "adantr.mm"
include "nnge1.mm"
include "cz.mm"
include "cuz.mm"
include "nn0z.mm"
include "adantl.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "leexp2ad.mm"
include "nnnn0.mm"
include "faclbnd.mm"
include "sylan.mm"
include "wi.mm"
include "nn0re.mm"
include "reexpcl.mm"
include "peano2nn0.mm"
include "syl2an.mm"
include "mpancom.mm"
include "faccl.mm"
include "nnred.mm"
include "remulcl.mm"
include "letr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "0exp.mm"
include "0le1.mm"
include "syl6eqbr.mm"
include "oveq2.mm"
include "0exp0e1.mm"
include "1le1.mm"
include "eqbrtri.mm"
include "jaoi.mm"
include "sylbi.mm"
include "1nn.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "nnge1d.mm"
include "0re.mm"
include "mpan.mm"
include "1re.mm"
include "mp3an2.mm"
include "syl2anc.mm"
include "wb.mm"
include "oveq1.mm"
include "oveq12.mm"
include "anidms.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "mpbird.mm"
include "jaoian.mm"
include "sylanb.mm"

theorem faclbnd3
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M ^ N ) <_ ( ( M ^ M ) x. ( ! ` N ) ) )

  proof
    cM
    cn0
    wcel
    #
    cM
    cn
    wcel
    #
    cM
    cc0
    wceq
    #
    wo
    cN
    cn0
    wcel
    #
    cM
    cN
    cexp
    co
    #
    cM
    cM
    cexp
    co
    #
    cN
    cfa
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cM
    elnn0
    @1
    @3
    @8
    @2
    @1
    @3
    wa
    #
    @4
    cM
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cle
    wbr
    #
    @11
    @7
    cle
    wbr
    #
    @8
    @9
    cM
    cN
    @10
    @1
    cM
    cr
    wcel
    #
    @3
    cM
    nnre
    adantr
    @1
    c1
    cM
    cle
    wbr
    @3
    cM
    nnge1
    adantr
    @9
    cN
    cz
    wcel
    #
    cN
    cN
    cuz
    cfv
    #
    wcel
    @10
    @16
    wcel
    @3
    @15
    @1
    cN
    nn0z
    adantl
    cN
    uzid
    cN
    cN
    peano2uz
    3syl
    leexp2ad
    @1
    @0
    @3
    @13
    cM
    nnnn0
    #
    cM
    cN
    faclbnd
    sylan
    @1
    @0
    @3
    @12
    @13
    wa
    @8
    wi
    #
    @17
    @0
    @3
    wa
    @4
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @18
    @0
    @14
    @3
    @19
    cM
    nn0re
    #
    cM
    cN
    reexpcl
    sylan
    @0
    @14
    @10
    cn0
    wcel
    @20
    @3
    @22
    cN
    peano2nn0
    cM
    @10
    reexpcl
    syl2an
    @0
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @21
    @3
    @14
    @0
    @23
    @22
    cM
    cM
    reexpcl
    mpancom
    @3
    @6
    cN
    faccl
    #
    nnred
    #
    @5
    @6
    remulcl
    syl2an
    @4
    @11
    @7
    letr
    syl3anc
    sylan
    mp2and
    @2
    @3
    wa
    @8
    cc0
    cN
    cexp
    co
    #
    c1
    @6
    cmul
    co
    #
    cle
    wbr
    #
    @3
    @29
    @2
    @3
    @27
    c1
    cle
    wbr
    #
    c1
    @28
    cle
    wbr
    #
    @29
    @3
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @30
    cN
    elnn0
    @32
    @30
    @33
    @32
    @27
    cc0
    c1
    cle
    cN
    0exp
    0le1
    syl6eqbr
    @33
    @27
    cc0
    cc0
    cexp
    co
    #
    c1
    cle
    cN
    cc0
    cc0
    cexp
    oveq2
    @34
    c1
    c1
    cle
    0exp0e1
    1le1
    eqbrtri
    syl6eqbr
    jaoi
    sylbi
    @3
    @28
    @3
    c1
    cn
    wcel
    @6
    cn
    wcel
    @28
    cn
    wcel
    1nn
    @25
    c1
    @6
    nnmulcl
    sylancr
    nnge1d
    @3
    @27
    cr
    wcel
    #
    @28
    cr
    wcel
    #
    @30
    @31
    wa
    @29
    wi
    #
    cc0
    cr
    wcel
    @3
    @35
    0re
    cc0
    cN
    reexpcl
    mpan
    @3
    c1
    cr
    wcel
    #
    @24
    @36
    1re
    @26
    c1
    @6
    remulcl
    sylancr
    @35
    @38
    @36
    @37
    1re
    @27
    c1
    @28
    letr
    mp3an2
    syl2anc
    mp2and
    adantl
    @2
    @8
    @29
    wb
    @3
    @2
    @4
    @27
    @7
    @28
    cle
    cM
    cc0
    cN
    cexp
    oveq1
    @2
    @5
    c1
    @6
    cmul
    @2
    @5
    @34
    c1
    @2
    @5
    @34
    wceq
    cM
    cc0
    cM
    cc0
    cexp
    oveq12
    anidms
    0exp0e1
    syl6eq
    oveq1d
    breq12d
    adantr
    mpbird
    jaoian
    sylanb
end
