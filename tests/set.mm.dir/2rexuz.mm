include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wrex.mm"
include "wex.mm"
include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "rexuz2.mm"
include "exbii.mm"
include "df-rex.mm"
include "bitr4i.mm"

theorem 2rexuz
  let wph: wff ph
  let vm: setvar m
  let vn: setvar n
  let cM: class M

  disjoint m n
  disjoint M m
  disjoint M n
  assert |- ( E. m E. n e. ( ZZ>= ` m ) ph <-> E. m e. ZZ E. n e. ZZ ( m <_ n /\ ph ) )

  proof
    wph
    vn
    vm
    cv
    #
    cuz
    cfv
    wrex
    #
    vm
    wex
    @0
    cz
    wcel
    @0
    vn
    cv
    cle
    wbr
    wph
    wa
    vn
    cz
    wrex
    #
    wa
    #
    vm
    wex
    @2
    vm
    cz
    wrex
    @1
    @3
    vm
    wph
    vn
    @0
    rexuz2
    exbii
    @2
    vm
    cz
    df-rex
    bitr4i
end
