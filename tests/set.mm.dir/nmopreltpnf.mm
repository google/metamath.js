include "chil.mm"
include "wf.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "nmoprepnf.mm"
include "cxr.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "nmopxr.mm"
include "nltpnft.mm"
include "syl.mm"
include "necon2abid.mm"
include "bitr4d.mm"

theorem nmopreltpnf
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T : ~H --> ~H -> ( ( normop ` T ) e. RR <-> ( normop ` T ) < +oo ) )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    cnop
    cfv
    #
    cr
    wcel
    @1
    cpnf
    wne
    @1
    cpnf
    clt
    wbr
    #
    cT
    nmoprepnf
    @0
    @2
    @1
    cpnf
    @0
    @1
    cxr
    wcel
    @1
    cpnf
    wceq
    @2
    wn
    wb
    cT
    nmopxr
    @1
    nltpnft
    syl
    necon2abid
    bitr4d
end
