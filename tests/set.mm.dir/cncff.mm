include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wa.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "cncfrss.mm"
include "cncfrss2.mm"
include "elcncf.mm"
include "syl2anc.mm"
include "ibi.mm"
include "simpld.mm"

theorem cncff
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cR: class R


  assert |- ( F e. ( A -cn-> B ) -> F : A --> B )

  proof
    cF
    cA
    cB
    ccncf
    co
    wcel
    #
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    vw
    cv
    #
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    @2
    cF
    cfv
    @3
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    wi
    vw
    cA
    wral
    vz
    crp
    wrex
    vy
    crp
    wral
    vx
    cA
    wral
    #
    @0
    @1
    @4
    wa
    #
    @0
    cA
    cc
    wss
    cB
    cc
    wss
    @0
    @5
    wb
    cA
    cB
    cF
    cncfrss
    cA
    cB
    cF
    cncfrss2
    vx
    vy
    vz
    vw
    cA
    cB
    cF
    elcncf
    syl2anc
    ibi
    simpld
end
