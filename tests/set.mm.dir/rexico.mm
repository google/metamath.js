include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "simpr.mm"
include "pnfxr.mm"
include "icossre.mm"
include "sylancl.mm"
include "ssrexv.mm"
include "syl.mm"
include "cif.mm"
include "simplr.mm"
include "ifcld.mm"
include "max1.mm"
include "adantll.mm"
include "wb.mm"
include "elicopnf.mm"
include "ad2antlr.mm"
include "mpbir2and.mm"
include "adantr.mm"
include "simpll.mm"
include "sselda.mm"
include "maxle.mm"
include "syl3anc.mm"
include "syl6bi.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "impbid.mm"

theorem rexico
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint j ph
  disjoint j n
  disjoint k n
  disjoint A n
  disjoint B n
  disjoint n ph
  assert |- ( ( A C_ RR /\ B e. RR ) -> ( E. j e. ( B [,) +oo ) A. k e. A ( j <_ k -> ph ) <-> E. j e. RR A. k e. A ( j <_ k -> ph ) ) )

  proof
    cA
    cr
    wss
    #
    cB
    cr
    wcel
    #
    wa
    #
    vj
    cv
    #
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
    cA
    wral
    #
    vj
    cB
    cpnf
    cico
    co
    #
    wrex
    #
    @7
    vj
    cr
    wrex
    #
    @2
    @8
    cr
    wss
    #
    @9
    @10
    wi
    @2
    @1
    cpnf
    cxr
    wcel
    @11
    @0
    @1
    simpr
    pnfxr
    cB
    cpnf
    icossre
    sylancl
    @7
    vj
    @8
    cr
    ssrexv
    syl
    @2
    @10
    vn
    cv
    #
    @4
    cle
    wbr
    #
    wph
    wi
    #
    vk
    cA
    wral
    #
    vn
    @8
    wrex
    #
    @9
    @2
    @7
    @16
    vj
    cr
    @2
    @3
    cr
    wcel
    #
    wa
    #
    cB
    @3
    cle
    wbr
    #
    @3
    cB
    cif
    #
    @8
    wcel
    #
    @7
    @20
    @4
    cle
    wbr
    #
    wph
    wi
    #
    vk
    cA
    wral
    #
    @16
    @18
    @21
    @20
    cr
    wcel
    #
    cB
    @20
    cle
    wbr
    #
    @18
    @19
    @3
    cB
    cr
    @2
    @17
    simpr
    @0
    @1
    @17
    simplr
    #
    ifcld
    @1
    @17
    @26
    @0
    cB
    @3
    max1
    adantll
    @1
    @21
    @25
    @26
    wa
    wb
    @0
    @17
    cB
    @20
    elicopnf
    ad2antlr
    mpbir2and
    @18
    @6
    @23
    vk
    cA
    @18
    @4
    cA
    wcel
    #
    wa
    #
    @22
    @5
    wph
    @29
    @22
    cB
    @4
    cle
    wbr
    #
    @5
    wa
    #
    @5
    @29
    @1
    @17
    @4
    cr
    wcel
    @22
    @31
    wb
    @18
    @1
    @28
    @27
    adantr
    @2
    @17
    @28
    simplr
    @18
    cA
    cr
    @4
    @0
    @1
    @17
    simpll
    sselda
    cB
    @3
    @4
    maxle
    syl3anc
    @30
    @5
    simpr
    syl6bi
    imim1d
    ralimdva
    @15
    @24
    vn
    @20
    @8
    @12
    @20
    wceq
    #
    @14
    @23
    vk
    cA
    @32
    @13
    @22
    wph
    @12
    @20
    @4
    cle
    breq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    @15
    @7
    vn
    vj
    @8
    @12
    @3
    wceq
    #
    @14
    @6
    vk
    cA
    @33
    @13
    @5
    wph
    @12
    @3
    @4
    cle
    breq1
    imbi1d
    ralbidv
    cbvrexv
    syl6ib
    impbid
end
