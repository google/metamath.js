include "cr.mm"
include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "remet.mm"
include "metxmet.mm"
include "ax-mp.mm"

theorem rexmet
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )


  assert |- D e. ( *Met ` RR )

  proof
    cD
    cr
    cme
    cfv
    wcel
    cD
    cr
    cxmt
    cfv
    wcel
    cD
    remet.1
    remet
    cD
    cr
    metxmet
    ax-mp
end
