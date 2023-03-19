include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "wss.mm"
include "cnmet.mm"
include "ax-resscn.mm"
include "metres2.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem remet
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )


  assert |- D e. ( Met ` RR )

  proof
    cD
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    cres
    #
    cr
    cme
    cfv
    #
    remet.1
    @0
    cc
    cme
    cfv
    wcel
    cr
    cc
    wss
    @1
    @2
    wcel
    cnmet
    ax-resscn
    @0
    cr
    cc
    metres2
    mp2an
    eqeltri
end
