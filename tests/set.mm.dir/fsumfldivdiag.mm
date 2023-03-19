include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "fsumfldivdiaglem.mm"
include "impbid.mm"
include "fsumcom2.mm"

theorem fsumfldivdiag
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  assume fsumfldivdiag.1: |- ( ph -> A e. RR )
  assume fsumfldivdiag.2: |- ( ( ph /\ ( n e. ( 1 ... ( |_ ` A ) ) /\ m e. ( 1 ... ( |_ ` ( A / n ) ) ) ) ) -> B e. CC )

  disjoint m n
  disjoint A m
  disjoint A n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> sum_ n e. ( 1 ... ( |_ ` A ) ) sum_ m e. ( 1 ... ( |_ ` ( A / n ) ) ) B = sum_ m e. ( 1 ... ( |_ ` A ) ) sum_ n e. ( 1 ... ( |_ ` ( A / m ) ) ) B )

  proof
    wph
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    c1
    cA
    vn
    cv
    #
    cdiv
    co
    cfl
    cfv
    #
    cfz
    co
    #
    @1
    c1
    cA
    vm
    cv
    #
    cdiv
    co
    cfl
    cfv
    cfz
    co
    #
    vn
    vm
    cB
    wph
    c1
    @0
    fzfid
    #
    @7
    wph
    @2
    @1
    wcel
    #
    wa
    c1
    @3
    fzfid
    wph
    @8
    @5
    @4
    wcel
    wa
    @5
    @1
    wcel
    @2
    @6
    wcel
    wa
    wph
    cA
    vm
    vn
    fsumfldivdiag.1
    fsumfldivdiaglem
    wph
    cA
    vn
    vm
    fsumfldivdiag.1
    fsumfldivdiaglem
    impbid
    fsumfldivdiag.2
    fsumcom2
end
