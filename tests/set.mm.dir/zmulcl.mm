include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "cn0.mm"
include "cneg.mm"
include "wo.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "elznn0.mm"
include "wi.mm"
include "nn0mulcl.mm"
include "orcd.mm"
include "a1i.mm"
include "remulcl.mm"
include "jctild.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "mulneg1.mm"
include "syl2an.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "olc.mm"
include "syl6.mm"
include "mulneg2.mm"
include "mul2neg.mm"
include "orc.mm"
include "ccased.mm"
include "syl6ibr.mm"
include "imp.mm"
include "an4s.mm"
include "syl2anb.mm"

theorem zmulcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M x. N ) e. ZZ )

  proof
    cM
    cz
    wcel
    cM
    cr
    wcel
    #
    cM
    cn0
    wcel
    #
    cM
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    wa
    cN
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    wa
    cM
    cN
    cmul
    co
    #
    cz
    wcel
    #
    cN
    cz
    wcel
    cM
    elznn0
    cN
    elznn0
    @0
    @5
    @4
    @9
    @11
    @0
    @5
    wa
    #
    @4
    @9
    wa
    #
    @11
    @12
    @13
    @10
    cr
    wcel
    #
    @10
    cn0
    wcel
    #
    @10
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    wa
    #
    @11
    @12
    @1
    @6
    @3
    @8
    @19
    @12
    @1
    @6
    wa
    #
    @18
    @14
    @20
    @18
    wi
    @12
    @20
    @15
    @17
    cM
    cN
    nn0mulcl
    orcd
    a1i
    cM
    cN
    remulcl
    #
    jctild
    @12
    @3
    @6
    wa
    #
    @18
    @14
    @12
    @22
    @17
    @18
    @22
    @2
    cN
    cmul
    co
    #
    cn0
    wcel
    @12
    @17
    @2
    cN
    nn0mulcl
    @12
    @23
    @16
    cn0
    @0
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @23
    @16
    wceq
    @5
    cM
    recn
    #
    cN
    recn
    #
    cM
    cN
    mulneg1
    syl2an
    eleq1d
    syl5ib
    @17
    @15
    olc
    #
    syl6
    @21
    jctild
    @12
    @1
    @8
    wa
    #
    @18
    @14
    @12
    @29
    @17
    @18
    @29
    cM
    @7
    cmul
    co
    #
    cn0
    wcel
    @12
    @17
    cM
    @7
    nn0mulcl
    @12
    @30
    @16
    cn0
    @0
    @24
    @25
    @30
    @16
    wceq
    @5
    @26
    @27
    cM
    cN
    mulneg2
    syl2an
    eleq1d
    syl5ib
    @28
    syl6
    @21
    jctild
    @12
    @3
    @8
    wa
    #
    @18
    @14
    @12
    @31
    @15
    @18
    @31
    @2
    @7
    cmul
    co
    #
    cn0
    wcel
    @12
    @15
    @2
    @7
    nn0mulcl
    @12
    @32
    @10
    cn0
    @0
    @24
    @25
    @32
    @10
    wceq
    @5
    @26
    @27
    cM
    cN
    mul2neg
    syl2an
    eleq1d
    syl5ib
    @15
    @17
    orc
    syl6
    @21
    jctild
    ccased
    @10
    elznn0
    syl6ibr
    imp
    an4s
    syl2anb
end
