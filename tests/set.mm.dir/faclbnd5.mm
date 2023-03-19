include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "caddc.mm"
include "cfa.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "nn0re.mm"
include "reexpcl.mm"
include "sylan.mm"
include "ancoms.mm"
include "nnre.mm"
include "remulcl.mm"
include "syl2an.mm"
include "anandirs.mm"
include "2nn.mm"
include "nn0sqcl.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnnn0.mm"
include "nn0addcl.mm"
include "sylan2.mm"
include "anabss7.mm"
include "nnmulcl.mm"
include "anabss5.mm"
include "nnred.mm"
include "faccl.mm"
include "2re.mm"
include "cle.mm"
include "faclbnd4.mm"
include "syl3an3.mm"
include "3coml.mm"
include "3expa.mm"
include "c1.mm"
include "1lt2.mm"
include "cc0.mm"
include "wb.mm"
include "nngt0d.mm"
include "ltmulgt12.mm"
include "mp3an2.mm"
include "syl2anc.mm"
include "mpbii.mm"
include "lelttrd.mm"
include "cc.mm"
include "wceq.mm"
include "nncnd.mm"
include "2cn.mm"
include "mulass.mm"
include "mp3an1.mm"
include "breqtrrd.mm"
include "3impa.mm"
include "3comr.mm"

theorem faclbnd5
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( N e. NN0 /\ K e. NN0 /\ M e. NN ) -> ( ( N ^ K ) x. ( M ^ N ) ) < ( ( 2 x. ( ( 2 ^ ( K ^ 2 ) ) x. ( M ^ ( M + K ) ) ) ) x. ( ! ` N ) ) )

  proof
    cK
    cn0
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cK
    cexp
    co
    #
    cM
    cN
    cexp
    co
    #
    cmul
    co
    #
    c2
    c2
    cK
    c2
    cexp
    co
    #
    cexp
    co
    #
    cM
    cM
    cK
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    cN
    cfa
    cfv
    #
    cmul
    co
    #
    clt
    wbr
    #
    @0
    @1
    @2
    @13
    @0
    @1
    wa
    #
    @2
    wa
    #
    @5
    c2
    @10
    @11
    cmul
    co
    #
    cmul
    co
    #
    @12
    clt
    @15
    @5
    @16
    @17
    @0
    @1
    @2
    @5
    cr
    wcel
    #
    @0
    @2
    wa
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @18
    @1
    @2
    wa
    @2
    @0
    @19
    @2
    cN
    cr
    wcel
    @0
    @19
    cN
    nn0re
    cN
    cK
    reexpcl
    sylan
    ancoms
    @1
    cM
    cr
    wcel
    @2
    @20
    cM
    nnre
    cM
    cN
    reexpcl
    sylan
    @3
    @4
    remulcl
    syl2an
    anandirs
    @14
    @10
    cr
    wcel
    @11
    cr
    wcel
    @16
    cr
    wcel
    #
    @2
    @14
    @10
    @0
    @1
    @10
    cn
    wcel
    #
    @0
    @7
    cn
    wcel
    #
    @9
    cn
    wcel
    #
    @22
    @14
    @0
    c2
    cn
    wcel
    @6
    cn0
    wcel
    @23
    2nn
    cK
    nn0sqcl
    c2
    @6
    nnexpcl
    sylancr
    @0
    @1
    @24
    @14
    @1
    @8
    cn0
    wcel
    #
    @24
    @1
    @0
    cM
    cn0
    wcel
    #
    @25
    cM
    nnnn0
    #
    @26
    @0
    @25
    cM
    cK
    nn0addcl
    ancoms
    sylan2
    cM
    @8
    nnexpcl
    sylan2
    anabss7
    @7
    @9
    nnmulcl
    syl2an
    anabss5
    #
    nnred
    @2
    @11
    cN
    faccl
    #
    nnred
    @10
    @11
    remulcl
    syl2an
    #
    @15
    c2
    cr
    wcel
    #
    @21
    @17
    cr
    wcel
    2re
    @30
    c2
    @16
    remulcl
    sylancr
    @0
    @1
    @2
    @5
    @16
    cle
    wbr
    #
    @2
    @0
    @1
    @32
    @1
    @2
    @0
    @26
    @32
    @27
    cK
    cM
    cN
    faclbnd4
    syl3an3
    3coml
    3expa
    @15
    c1
    c2
    clt
    wbr
    #
    @16
    @17
    clt
    wbr
    #
    1lt2
    @15
    @21
    cc0
    @16
    clt
    wbr
    #
    @33
    @34
    wb
    #
    @30
    @15
    @16
    @14
    @22
    @11
    cn
    wcel
    @16
    cn
    wcel
    @2
    @28
    @29
    @10
    @11
    nnmulcl
    syl2an
    nngt0d
    @21
    @31
    @35
    @36
    2re
    @16
    c2
    ltmulgt12
    mp3an2
    syl2anc
    mpbii
    lelttrd
    @14
    @10
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @12
    @17
    wceq
    #
    @2
    @14
    @10
    @28
    nncnd
    @2
    @11
    @29
    nncnd
    c2
    cc
    wcel
    @37
    @38
    @39
    2cn
    c2
    @10
    @11
    mulass
    mp3an1
    syl2an
    breqtrrd
    3impa
    3comr
end
