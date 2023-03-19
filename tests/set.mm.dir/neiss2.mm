include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wa.mm"
include "cdm.mm"
include "cpw.mm"
include "elfvdm.mm"
include "adantl.mm"
include "wb.mm"
include "wfn.mm"
include "wceq.mm"
include "neif.mm"
include "fndm.mm"
include "syl.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mpbid.mm"
include "elpwid.mm"

theorem neiss2
  let cS: class S
  let cJ: class J
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  assume neifval.1: |- X = U. J


  assert |- ( ( J e. Top /\ N e. ( ( nei ` J ) ` S ) ) -> S C_ X )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cS
    cJ
    cnei
    cfv
    #
    cfv
    wcel
    #
    wa
    #
    cS
    cX
    @3
    cS
    @1
    cdm
    #
    wcel
    #
    cS
    cX
    cpw
    #
    wcel
    #
    @2
    @5
    @0
    cN
    cS
    @1
    elfvdm
    adantl
    @0
    @5
    @7
    wb
    @2
    @0
    @4
    @6
    cS
    @0
    @1
    @6
    wfn
    @4
    @6
    wceq
    cJ
    cX
    neifval.1
    neif
    @6
    @1
    fndm
    syl
    eleq2d
    adantr
    mpbid
    elpwid
end
