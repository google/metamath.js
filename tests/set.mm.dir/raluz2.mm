include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "w3a.mm"
include "eluz2.mm"
include "3anass.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "imbi2i.mm"
include "bi2.04.mm"
include "ralbii2.mm"
include "r19.21v.mm"

theorem raluz2
  let wph: wff ph
  let vn: setvar n
  let cM: class M
  let vm: setvar m

  disjoint M n
  disjoint m n
  disjoint M m
  assert |- ( A. n e. ( ZZ>= ` M ) ph <-> ( M e. ZZ -> A. n e. ZZ ( M <_ n -> ph ) ) )

  proof
    wph
    vn
    cM
    cuz
    cfv
    #
    wral
    cM
    cz
    wcel
    #
    cM
    vn
    cv
    #
    cle
    wbr
    #
    wph
    wi
    #
    wi
    #
    vn
    cz
    wral
    @1
    @4
    vn
    cz
    wral
    wi
    wph
    @5
    vn
    @0
    cz
    @2
    @0
    wcel
    #
    wph
    wi
    @1
    @2
    cz
    wcel
    #
    @3
    wa
    #
    wa
    #
    wph
    wi
    #
    @7
    @5
    wi
    #
    @6
    @9
    wph
    @6
    @1
    @7
    @3
    w3a
    @9
    cM
    @2
    eluz2
    @1
    @7
    @3
    3anass
    bitri
    imbi1i
    @10
    @1
    @7
    @4
    wi
    #
    wi
    #
    @11
    @10
    @1
    @8
    wph
    wi
    #
    wi
    @13
    @1
    @8
    wph
    impexp
    @14
    @12
    @1
    @7
    @3
    wph
    impexp
    imbi2i
    bitri
    @1
    @7
    @4
    bi2.04
    bitri
    bitri
    ralbii2
    @1
    @4
    vn
    cz
    r19.21v
    bitri
end
