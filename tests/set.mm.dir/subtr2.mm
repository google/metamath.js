include "wcel.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "cv.mm"
include "nfeq.mm"
include "nfbi.mm"
include "nfim.mm"
include "eqeq1.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "adantr.mm"

theorem subtr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume subtr.1: |- F/_ x A
  assume subtr.2: |- F/_ x B
  assume subtr2.3: |- F/ x ps
  assume subtr2.4: |- F/ x ch
  assume subtr2.5: |- ( x = A -> ( ph <-> ps ) )
  assume subtr2.6: |- ( x = B -> ( ph <-> ch ) )


  assert |- ( ( A e. C /\ B e. D ) -> ( A = B -> ( ps <-> ch ) ) )

  proof
    cA
    cC
    wcel
    cA
    cB
    wceq
    #
    wps
    wch
    wb
    #
    wi
    #
    cB
    cD
    wcel
    vx
    cv
    #
    cB
    wceq
    #
    wph
    wch
    wb
    #
    wi
    @2
    vx
    cA
    cC
    subtr.1
    @0
    @1
    vx
    vx
    cA
    cB
    subtr.1
    subtr.2
    nfeq
    wps
    wch
    vx
    subtr2.3
    subtr2.4
    nfbi
    nfim
    @3
    cA
    wceq
    #
    @4
    @0
    @5
    @1
    @3
    cA
    cB
    eqeq1
    @6
    wph
    wps
    wch
    subtr2.5
    bibi1d
    imbi12d
    subtr2.6
    vtoclgf
    adantr
end
