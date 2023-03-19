include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "eluz1.mm"
include "anbi1d.mm"
include "anass.mm"
include "syl6bb.mm"
include "rexbidv2.mm"

theorem rexuz
  let wph: wff ph
  let vn: setvar n
  let cM: class M
  let vm: setvar m

  disjoint M n
  disjoint m n
  disjoint M m
  assert |- ( M e. ZZ -> ( E. n e. ( ZZ>= ` M ) ph <-> E. n e. ZZ ( M <_ n /\ ph ) ) )

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
    wa
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
    wa
    @1
    cz
    wcel
    #
    @2
    wa
    #
    wph
    wa
    @6
    @3
    wa
    @0
    @5
    @7
    wph
    cM
    @1
    eluz1
    anbi1d
    @6
    @2
    wph
    anass
    syl6bb
    rexbidv2
end
