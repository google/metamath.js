include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cab.mm"
include "wceq.mm"
include "wb.mm"
include "abidnf.mm"
include "eqcomd.mm"
include "syl.mm"
include "mpbiri.mm"

theorem dedhb
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  assume dedhb.1: |- ( A = { z | A. x z e. A } -> ( ph <-> ps ) )
  assume dedhb.2: |- ps

  disjoint x z
  disjoint A z
  assert |- ( F/_ x A -> ph )

  proof
    vx
    cA
    wnfc
    #
    wph
    wps
    dedhb.2
    @0
    cA
    vz
    cv
    cA
    wcel
    vx
    wal
    vz
    cab
    #
    wceq
    wph
    wps
    wb
    @0
    @1
    cA
    vx
    vz
    cA
    abidnf
    eqcomd
    dedhb.1
    syl
    mpbiri
end
