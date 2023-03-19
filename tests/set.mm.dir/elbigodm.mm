include "cbigo.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cdm.mm"
include "cpnf.mm"
include "cico.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "wss.mm"
include "elbigo.mm"
include "wf.mm"
include "reex.mm"
include "elpm2.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "sylbi.mm"

theorem elbigodm
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vf: setvar f
  let vx: setvar x
  let vm: setvar m
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let vk: setvar k


  assert |- ( F e. ( _O ` G ) -> dom F C_ RR )

  proof
    cF
    cG
    cbigo
    cfv
    wcel
    cF
    cr
    cr
    cpm
    co
    #
    wcel
    #
    cG
    @0
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    vm
    cv
    @3
    cG
    cfv
    cmul
    co
    cle
    wbr
    vy
    cF
    cdm
    #
    vx
    cv
    cpnf
    cico
    co
    cin
    wral
    vm
    cr
    wrex
    vx
    cr
    wrex
    #
    w3a
    @4
    cr
    wss
    #
    vx
    vy
    vm
    cF
    cG
    elbigo
    @1
    @2
    @6
    @5
    @1
    @4
    cr
    cF
    wf
    @6
    cr
    cr
    cF
    reex
    reex
    elpm2
    simprbi
    3ad2ant1
    sylbi
end
