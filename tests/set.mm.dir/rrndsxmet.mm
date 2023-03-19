include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "rrndsmet.mm"
include "metxmet.mm"
include "syl.mm"

theorem rrndsxmet
  let wph: wff ph
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cX: class X
  let vx: setvar x
  assume rrndsxmet.1: |- ( ph -> X e. Fin )
  assume rrndsxmet.2: |- D = ( f e. ( RR ^m X ) , g e. ( RR ^m X ) |-> ( sqrt ` sum_ k e. X ( ( ( f ` k ) - ( g ` k ) ) ^ 2 ) ) )

  disjoint X f
  disjoint X g
  disjoint X k
  disjoint f g
  disjoint f k
  disjoint g k
  disjoint k x
  assert |- ( ph -> D e. ( *Met ` ( RR ^m X ) ) )

  proof
    wph
    cD
    cr
    cX
    cmap
    co
    #
    cme
    cfv
    wcel
    cD
    @0
    cxmt
    cfv
    wcel
    wph
    cD
    vf
    vg
    vk
    cX
    rrndsxmet.1
    rrndsxmet.2
    rrndsmet
    cD
    @0
    metxmet
    syl
end
