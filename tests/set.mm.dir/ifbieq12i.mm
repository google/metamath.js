include "cif.mm"
include "wceq.mm"
include "ifeq1.mm"
include "ax-mp.mm"
include "ifbieq2i.mm"
include "eqtri.mm"

theorem ifbieq12i
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ifbieq12i.1: |- ( ph <-> ps )
  assume ifbieq12i.2: |- A = C
  assume ifbieq12i.3: |- B = D


  assert |- if ( ph , A , B ) = if ( ps , C , D )

  proof
    wph
    cA
    cB
    cif
    #
    wph
    cC
    cB
    cif
    #
    wps
    cC
    cD
    cif
    cA
    cC
    wceq
    @0
    @1
    wceq
    ifbieq12i.2
    wph
    cA
    cC
    cB
    ifeq1
    ax-mp
    wph
    wps
    cB
    cD
    cC
    ifbieq12i.1
    ifbieq12i.3
    ifbieq2i
    eqtri
end
