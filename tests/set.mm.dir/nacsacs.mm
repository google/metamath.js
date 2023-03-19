include "cnacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cacs.mm"
include "cmrc.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "wceq.mm"
include "eqid.mm"
include "isnacs2.mm"
include "simplbi.mm"

theorem nacsacs
  let cC: class C
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vs: setvar s
  let vt: setvar t


  assert |- ( C e. ( NoeACS ` X ) -> C e. ( ACS ` X ) )

  proof
    cC
    cX
    cnacs
    cfv
    wcel
    cC
    cX
    cacs
    cfv
    wcel
    cC
    cmrc
    cfv
    #
    cX
    cpw
    cfn
    cin
    cima
    cC
    wceq
    cC
    @0
    cX
    @0
    eqid
    isnacs2
    simplbi
end
