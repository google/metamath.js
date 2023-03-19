include "wcel.mm"
include "wceq.mm"
include "cfv.mm"
include "csb.mm"
include "cif.mm"
include "cdlemk40.mm"
include "iftrue.mm"
include "sylan9eqr.mm"

theorem cdlemk40t
  let wph: wff ph
  let vz: setvar z
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cN: class N
  let cX: class X
  assume cdlemk40.x: |- X = ( iota_ z e. T ph )
  assume cdlemk40.u: |- U = ( g e. T |-> if ( F = N , g , X ) )

  disjoint F g
  disjoint N g
  disjoint T g
  assert |- ( ( F = N /\ G e. T ) -> ( U ` G ) = G )

  proof
    cG
    cT
    wcel
    cF
    cN
    wceq
    #
    cG
    cU
    cfv
    @0
    cG
    vg
    cG
    cX
    csb
    #
    cif
    cG
    wph
    vz
    cT
    cU
    vg
    cF
    cG
    cN
    cX
    cdlemk40.x
    cdlemk40.u
    cdlemk40
    @0
    cG
    @1
    iftrue
    sylan9eqr
end
