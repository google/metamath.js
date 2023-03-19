include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "wa.mm"
include "clvec.mm"
include "lmodpropd.mm"
include "eqtr3d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "islvec.mm"
include "3bitr4g.mm"

theorem lvecpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cF: class F
  let cK: class K
  let cL: class L
  assume lvecpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume lvecpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume lvecpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume lvecpropd.4: |- ( ph -> F = ( Scalar ` K ) )
  assume lvecpropd.5: |- ( ph -> F = ( Scalar ` L ) )
  assume lvecpropd.6: |- P = ( Base ` F )
  assume lvecpropd.7: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( K e. LVec <-> L e. LVec ) )

  proof
    wph
    cK
    clmod
    wcel
    #
    cK
    csca
    cfv
    #
    cdr
    wcel
    #
    wa
    cL
    clmod
    wcel
    #
    cL
    csca
    cfv
    #
    cdr
    wcel
    #
    wa
    cK
    clvec
    wcel
    cL
    clvec
    wcel
    wph
    @0
    @3
    @2
    @5
    wph
    vx
    vy
    cB
    cP
    cF
    cK
    cL
    lvecpropd.1
    lvecpropd.2
    lvecpropd.3
    lvecpropd.4
    lvecpropd.5
    lvecpropd.6
    lvecpropd.7
    lmodpropd
    wph
    @1
    @4
    cdr
    wph
    cF
    @1
    @4
    lvecpropd.4
    lvecpropd.5
    eqtr3d
    eleq1d
    anbi12d
    @1
    cK
    @1
    eqid
    islvec
    @4
    cL
    @4
    eqid
    islvec
    3bitr4g
end
