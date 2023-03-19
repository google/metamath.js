include "wsb.mm"
include "wsbc.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "dfsbcq2.mm"
include "sbequ.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "sbequ12.mm"
include "oveq1.mm"
include "sbceq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "uzind4.mm"

theorem uzind4s
  let wph: wff ph
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vj: setvar j
  assume uzind4s.1: |- ( M e. ZZ -> [. M / k ]. ph )
  assume uzind4s.2: |- ( k e. ( ZZ>= ` M ) -> ( ph -> [. ( k + 1 ) / k ]. ph ) )

  disjoint M k
  disjoint k m
  disjoint j m
  disjoint M m
  disjoint j k
  disjoint M j
  disjoint N j
  disjoint j ph
  disjoint m ph
  assert |- ( N e. ( ZZ>= ` M ) -> [. N / k ]. ph )

  proof
    wph
    vk
    vj
    wsb
    wph
    vk
    cM
    wsbc
    wph
    vk
    vm
    wsb
    #
    wph
    vk
    vm
    cv
    #
    c1
    caddc
    co
    #
    wsbc
    #
    wph
    vk
    cN
    wsbc
    vj
    vm
    cM
    cN
    wph
    vk
    vj
    cM
    dfsbcq2
    wph
    vj
    vm
    vk
    sbequ
    wph
    vk
    vj
    @2
    dfsbcq2
    wph
    vk
    vj
    cN
    dfsbcq2
    uzind4s.1
    vk
    cv
    #
    cM
    cuz
    cfv
    #
    wcel
    #
    wph
    wph
    vk
    @4
    c1
    caddc
    co
    #
    wsbc
    #
    wi
    #
    wi
    @1
    @5
    wcel
    #
    @0
    @3
    wi
    #
    wi
    vk
    vm
    @10
    @11
    vk
    @10
    vk
    nfv
    @0
    @3
    vk
    wph
    vk
    vm
    nfs1v
    wph
    vk
    @2
    nfsbc1v
    nfim
    nfim
    vk
    vm
    weq
    #
    @6
    @10
    @9
    @11
    @4
    @1
    @5
    eleq1
    @12
    wph
    @0
    @8
    @3
    wph
    vk
    vm
    sbequ12
    @12
    wph
    vk
    @7
    @2
    @4
    @1
    c1
    caddc
    oveq1
    sbceq1d
    imbi12d
    imbi12d
    uzind4s.2
    chvar
    uzind4
end
