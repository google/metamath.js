include "wcel.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "csb.mm"
include "cif.mm"
include "cdlemk40.mm"
include "ifnefalse.mm"
include "sylan9eqr.mm"

theorem cdlemk40f
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
  assert |- ( ( F =/= N /\ G e. T ) -> ( U ` G ) = [_ G / g ]_ X )

  proof
    cG
    cT
    wcel
    cF
    cN
    wne
    cG
    cU
    cfv
    cF
    cN
    wceq
    cG
    vg
    cG
    cX
    csb
    #
    cif
    @0
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
    cF
    cN
    cG
    @0
    ifnefalse
    sylan9eqr
end
