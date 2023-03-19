include "wceq.mm"
include "wa.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "co.mm"
include "simpr.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "axtgcgrid.mm"
include "eqtrd.mm"
include "impbida.mm"

theorem tgcgreqb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgcgrcomlr.a: |- ( ph -> A e. P )
  assume tgcgrcomlr.b: |- ( ph -> B e. P )
  assume tgcgrcomlr.c: |- ( ph -> C e. P )
  assume tgcgrcomlr.d: |- ( ph -> D e. P )
  assume tgcgrcomlr.6: |- ( ph -> ( A .- B ) = ( C .- D ) )


  assert |- ( ph -> ( A = B <-> C = D ) )

  proof
    wph
    cA
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    wph
    @0
    wa
    #
    cP
    cG
    cI
    c.mi
    cC
    cD
    cB
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    tkgeom.g
    adantr
    wph
    cC
    cP
    wcel
    @0
    tgcgrcomlr.c
    adantr
    wph
    cD
    cP
    wcel
    #
    @0
    tgcgrcomlr.d
    adantr
    wph
    cB
    cP
    wcel
    #
    @0
    tgcgrcomlr.b
    adantr
    @2
    cA
    cB
    c.mi
    co
    #
    cC
    cD
    c.mi
    co
    #
    cB
    cB
    c.mi
    co
    wph
    @6
    @7
    wceq
    #
    @0
    tgcgrcomlr.6
    adantr
    @2
    cA
    cB
    cB
    c.mi
    wph
    @0
    simpr
    oveq1d
    eqtr3d
    axtgcgrid
    wph
    @1
    wa
    #
    cP
    cG
    cI
    c.mi
    cA
    cB
    cD
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    @3
    @1
    tkgeom.g
    adantr
    wph
    cA
    cP
    wcel
    @1
    tgcgrcomlr.a
    adantr
    wph
    @5
    @1
    tgcgrcomlr.b
    adantr
    wph
    @4
    @1
    tgcgrcomlr.d
    adantr
    @9
    @6
    @7
    cD
    cD
    c.mi
    co
    wph
    @8
    @1
    tgcgrcomlr.6
    adantr
    @9
    cC
    cD
    cD
    c.mi
    wph
    @1
    simpr
    oveq1d
    eqtrd
    axtgcgrid
    impbida
end
