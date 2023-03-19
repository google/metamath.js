include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cr.mm"
include "wa.mm"
include "eluzelre.mm"
include "eleq2s.mm"
include "adantr.mm"
include "wb.mm"
include "eluzelz.mm"
include "eluz.mm"
include "syl2an.mm"
include "biimprd.mm"
include "expimpd.mm"
include "imim1d.mm"
include "exp4a.mm"
include "ralimdv2.mm"
include "imp.mm"
include "jca.mm"
include "reximi2.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cif.mm"
include "simpl.mm"
include "flcl.mm"
include "adantl.mm"
include "peano2zd.mm"
include "ifcld.mm"
include "zre.mm"
include "reflcl.mm"
include "peano2re.mm"
include "syl.mm"
include "max1.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "syl6eleqr.mm"
include "impexp.mm"
include "wss.mm"
include "uzss.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "simplr.mm"
include "zred.mm"
include "simpr.mm"
include "fllep1.mm"
include "max2.mm"
include "letrd.mm"
include "eluzle.mm"
include "ex.mm"
include "syl5bir.mm"
include "wceq.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "impbid2.mm"

theorem rexuzre
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  assume rexuz3.1: |- Z = ( ZZ>= ` M )

  disjoint M j
  disjoint j ph
  disjoint j k
  disjoint Z j
  disjoint Z k
  disjoint M k
  disjoint j m
  disjoint M m
  disjoint m ph
  disjoint k m
  disjoint Z m
  assert |- ( M e. ZZ -> ( E. j e. Z A. k e. ( ZZ>= ` j ) ph <-> E. j e. RR A. k e. Z ( j <_ k -> ph ) ) )

  proof
    cM
    cz
    wcel
    #
    wph
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
    cZ
    wrex
    #
    @1
    vk
    cv
    #
    cle
    wbr
    #
    wph
    wi
    #
    vk
    cZ
    wral
    #
    vj
    cr
    wrex
    #
    @3
    @8
    vj
    cZ
    cr
    @1
    cZ
    wcel
    #
    @3
    wa
    @1
    cr
    wcel
    #
    @8
    @10
    @11
    @3
    @11
    @1
    cM
    cuz
    cfv
    #
    cZ
    cM
    @1
    eluzelre
    rexuz3.1
    eleq2s
    adantr
    @10
    @3
    @8
    @10
    wph
    @7
    vk
    @2
    cZ
    @10
    @5
    @2
    wcel
    #
    wph
    wi
    @5
    cZ
    wcel
    #
    @6
    wph
    @10
    @14
    @6
    wa
    #
    @13
    wph
    @10
    @14
    @6
    @13
    @10
    @14
    wa
    @13
    @6
    @10
    @1
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @13
    @6
    wb
    @14
    @16
    @1
    @12
    cZ
    cM
    @1
    eluzelz
    rexuz3.1
    eleq2s
    @17
    @5
    @12
    cZ
    cM
    @5
    eluzelz
    rexuz3.1
    eleq2s
    @1
    @5
    eluz
    syl2an
    biimprd
    expimpd
    imim1d
    exp4a
    ralimdv2
    imp
    jca
    reximi2
    @0
    @9
    wph
    vk
    vm
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vm
    cZ
    wrex
    #
    @4
    @0
    @8
    @21
    vj
    cr
    @0
    @11
    wa
    #
    cM
    @1
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @24
    cM
    cif
    #
    cZ
    wcel
    @8
    wph
    vk
    @26
    cuz
    cfv
    #
    wral
    #
    @21
    @22
    @26
    @12
    cZ
    @22
    @0
    @26
    cz
    wcel
    #
    cM
    @26
    cle
    wbr
    #
    @26
    @12
    wcel
    #
    @0
    @11
    simpl
    #
    @22
    @25
    @24
    cM
    cz
    @22
    @23
    @11
    @23
    cz
    wcel
    @0
    @1
    flcl
    adantl
    peano2zd
    @32
    ifcld
    #
    @0
    cM
    cr
    wcel
    #
    @24
    cr
    wcel
    #
    @30
    @11
    cM
    zre
    #
    @11
    @23
    cr
    wcel
    @35
    @1
    reflcl
    @23
    peano2re
    syl
    #
    cM
    @24
    max1
    syl2an
    cM
    @26
    eluz2
    syl3anbrc
    #
    rexuz3.1
    syl6eleqr
    @22
    @7
    wph
    vk
    cZ
    @27
    @14
    @7
    wi
    @15
    wph
    wi
    @22
    @5
    @27
    wcel
    #
    wph
    wi
    @14
    @6
    wph
    impexp
    @22
    @39
    @15
    wph
    @22
    @39
    @15
    @22
    @39
    wa
    #
    @14
    @6
    @22
    @27
    cZ
    @5
    @22
    @27
    @12
    cZ
    @22
    @31
    @27
    @12
    wss
    @38
    cM
    @26
    uzss
    syl
    rexuz3.1
    syl6sseqr
    sselda
    @40
    @1
    @26
    @5
    @0
    @11
    @39
    simplr
    @40
    @26
    @22
    @29
    @39
    @33
    adantr
    zred
    @39
    @5
    cr
    wcel
    @22
    @26
    @5
    eluzelre
    adantl
    @22
    @1
    @26
    cle
    wbr
    @39
    @22
    @1
    @24
    @26
    @0
    @11
    simpr
    @11
    @35
    @0
    @37
    adantl
    @22
    @26
    @33
    zred
    @11
    @1
    @24
    cle
    wbr
    @0
    @1
    fllep1
    adantl
    @0
    @34
    @35
    @24
    @26
    cle
    wbr
    @11
    @36
    @37
    cM
    @24
    max2
    syl2an
    letrd
    adantr
    @39
    @26
    @5
    cle
    wbr
    @22
    @26
    @5
    eluzle
    adantl
    letrd
    jca
    ex
    imim1d
    syl5bir
    ralimdv2
    @20
    @28
    vm
    @26
    cZ
    @18
    @26
    wceq
    wph
    vk
    @19
    @27
    @18
    @26
    cuz
    fveq2
    raleqdv
    rspcev
    syl6an
    rexlimdva
    @20
    @3
    vm
    vj
    cZ
    @18
    @1
    wceq
    wph
    vk
    @19
    @2
    @18
    @1
    cuz
    fveq2
    raleqdv
    cbvrexv
    syl6ib
    impbid2
end
