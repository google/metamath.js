include "cuz.mm"
include "cfv.mm"
include "wrex.mm"
include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "eluz2.mm"
include "df-3an.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "an12.mm"
include "rexbii2.mm"
include "r19.42v.mm"

theorem rexuz2
  let wph: wff ph
  let vn: setvar n
  let cM: class M
  let vm: setvar m

  disjoint M n
  disjoint m n
  disjoint M m
  assert |- ( E. n e. ( ZZ>= ` M ) ph <-> ( M e. ZZ /\ E. n e. ZZ ( M <_ n /\ ph ) ) )

  proof
    wph
    vn
    cM
    cuz
    cfv
    #
    wrex
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
    wa
    #
    wa
    #
    vn
    cz
    wrex
    @1
    @4
    vn
    cz
    wrex
    wa
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
    wa
    @1
    @2
    cz
    wcel
    #
    wa
    #
    @3
    wa
    #
    wph
    wa
    #
    @7
    @5
    wa
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
    df-3an
    bitri
    anbi1i
    @10
    @8
    @4
    wa
    #
    @11
    @8
    @3
    wph
    anass
    @12
    @1
    @7
    @4
    wa
    wa
    @11
    @1
    @7
    @4
    anass
    @1
    @7
    @4
    an12
    bitri
    bitri
    bitri
    rexbii2
    @1
    @4
    vn
    cz
    r19.42v
    bitri
end
