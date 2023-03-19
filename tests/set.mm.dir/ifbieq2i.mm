include "cif.mm"
include "wb.mm"
include "wceq.mm"
include "ifbi.mm"
include "ax-mp.mm"
include "ifeq2.mm"
include "eqtri.mm"

theorem ifbieq2i
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifbieq2i.1: |- ( ph <-> ps )
  assume ifbieq2i.2: |- A = B


  assert |- if ( ph , C , A ) = if ( ps , C , B )

  proof
    wph
    cC
    cA
    cif
    #
    wps
    cC
    cA
    cif
    #
    wps
    cC
    cB
    cif
    #
    wph
    wps
    wb
    @0
    @1
    wceq
    ifbieq2i.1
    wph
    wps
    cC
    cA
    ifbi
    ax-mp
    cA
    cB
    wceq
    @1
    @2
    wceq
    ifbieq2i.2
    wps
    cA
    cB
    cC
    ifeq2
    ax-mp
    eqtri
end
