include "cif.mm"
include "ifbid.mm"
include "ifeq2d.mm"
include "eqtrd.mm"

theorem ifbieq2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifbieq2d.1: |- ( ph -> ( ps <-> ch ) )
  assume ifbieq2d.2: |- ( ph -> A = B )


  assert |- ( ph -> if ( ps , C , A ) = if ( ch , C , B ) )

  proof
    wph
    wps
    cC
    cA
    cif
    wch
    cC
    cA
    cif
    wch
    cC
    cB
    cif
    wph
    wps
    wch
    cC
    cA
    ifbieq2d.1
    ifbid
    wph
    wch
    cA
    cB
    cC
    ifbieq2d.2
    ifeq2d
    eqtrd
end
