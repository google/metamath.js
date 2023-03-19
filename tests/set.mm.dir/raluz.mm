include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "eluz1.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "ralbidv2.mm"

theorem raluz
  let wph: wff ph
  let vn: setvar n
  let cM: class M
  let vm: setvar m

  disjoint M n
  disjoint m n
  disjoint M m
  assert |- ( M e. ZZ -> ( A. n e. ( ZZ>= ` M ) ph <-> A. n e. ZZ ( M <_ n -> ph ) ) )

  proof
    cM
    cz
    wcel
    #
    wph
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
    vn
    cM
    cuz
    cfv
    #
    cz
    @0
    @1
    @4
    wcel
    #
    wph
    wi
    @1
    cz
    wcel
    #
    @2
    wa
    #
    wph
    wi
    @6
    @3
    wi
    @0
    @5
    @7
    wph
    cM
    @1
    eluz1
    imbi1d
    @6
    @2
    wph
    impexp
    syl6bb
    ralbidv2
end
