include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wi.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "elnnuz.mm"
include "uztrn.mm"
include "sylan2b.mm"
include "sylibr.mm"
include "expcom.mm"
include "eluzle.mm"
include "a1i.mm"
include "jcad.mm"
include "cz.mm"
include "nnz.mm"
include "w3a.mm"
include "eluz2.mm"
include "biimpri.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "3expib.mm"
include "impbid.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"

theorem climuzcnv
  let wph: wff ph
  let vk: setvar k
  let vm: setvar m

  disjoint k m
  assert |- ( m e. NN -> ( ( k e. ( ZZ>= ` m ) -> ph ) <-> ( k e. NN -> ( m <_ k -> ph ) ) ) )

  proof
    vm
    cv
    #
    cn
    wcel
    #
    vk
    cv
    #
    @0
    cuz
    cfv
    wcel
    #
    wph
    wi
    @2
    cn
    wcel
    #
    @0
    @2
    cle
    wbr
    #
    wa
    #
    wph
    wi
    @4
    @5
    wph
    wi
    wi
    @1
    @3
    @6
    wph
    @1
    @3
    @6
    @1
    @3
    @4
    @5
    @3
    @1
    @4
    @3
    @1
    wa
    @2
    c1
    cuz
    cfv
    #
    wcel
    #
    @4
    @1
    @3
    @0
    @7
    wcel
    @8
    @0
    elnnuz
    @0
    @2
    c1
    uztrn
    sylan2b
    @2
    elnnuz
    sylibr
    expcom
    @3
    @5
    wi
    @1
    @0
    @2
    eluzle
    a1i
    jcad
    @1
    @4
    @5
    @3
    @4
    @1
    @2
    cz
    wcel
    #
    @5
    @3
    @2
    nnz
    @1
    @0
    cz
    wcel
    #
    @9
    @5
    @3
    @0
    nnz
    @3
    @10
    @9
    @5
    w3a
    @0
    @2
    eluz2
    biimpri
    syl3an1
    syl3an2
    3expib
    impbid
    imbi1d
    @4
    @5
    wph
    impexp
    syl6bb
end
