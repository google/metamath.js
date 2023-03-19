include "cv.mm"
include "wsbc.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "dfsbcq.mm"
include "wi.mm"
include "cuz.mm"
include "cfv.mm"
include "weq.mm"
include "oveq1.mm"
include "sbceq1d.mm"
include "imbi12d.mm"
include "vtoclga.mm"
include "uzind4.mm"

theorem uzind4s2
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  assume uzind4s2.1: |- ( M e. ZZ -> [. M / j ]. ph )
  assume uzind4s2.2: |- ( k e. ( ZZ>= ` M ) -> ( [. k / j ]. ph -> [. ( k + 1 ) / j ]. ph ) )

  disjoint M k
  disjoint k ph
  disjoint j k
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint M m
  disjoint M n
  disjoint N m
  disjoint m ph
  disjoint n ph
  disjoint j m
  disjoint j n
  assert |- ( N e. ( ZZ>= ` M ) -> [. N / j ]. ph )

  proof
    wph
    vj
    vm
    cv
    #
    wsbc
    wph
    vj
    cM
    wsbc
    wph
    vj
    vn
    cv
    #
    wsbc
    #
    wph
    vj
    @1
    c1
    caddc
    co
    #
    wsbc
    #
    wph
    vj
    cN
    wsbc
    vm
    vn
    cM
    cN
    wph
    vj
    @0
    cM
    dfsbcq
    wph
    vj
    @0
    @1
    dfsbcq
    wph
    vj
    @0
    @3
    dfsbcq
    wph
    vj
    @0
    cN
    dfsbcq
    uzind4s2.1
    wph
    vj
    vk
    cv
    #
    wsbc
    #
    wph
    vj
    @5
    c1
    caddc
    co
    #
    wsbc
    #
    wi
    @2
    @4
    wi
    vk
    @1
    cM
    cuz
    cfv
    vk
    vn
    weq
    #
    @6
    @2
    @8
    @4
    wph
    vj
    @5
    @1
    dfsbcq
    @9
    wph
    vj
    @7
    @3
    @5
    @1
    c1
    caddc
    oveq1
    sbceq1d
    imbi12d
    uzind4s2.2
    vtoclga
    uzind4
end
