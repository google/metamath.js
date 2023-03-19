include "cbigo.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "elfvdm.mm"
include "cv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "crab.mm"
include "cmpt.mm"
include "df-bigo.mm"
include "dmeqi.mm"
include "cvv.mm"
include "wceq.mm"
include "dmmptg.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "mprg.mm"
include "eqtri.mm"
include "syl6eleq.mm"

theorem elbigofrcl
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vf: setvar f
  let vx: setvar x
  let vm: setvar m
  let vy: setvar y
  let vk: setvar k


  assert |- ( F e. ( _O ` G ) -> G e. ( RR ^pm RR ) )

  proof
    cF
    cG
    cbigo
    cfv
    wcel
    cG
    cbigo
    cdm
    #
    cr
    cr
    cpm
    co
    #
    cF
    cG
    cbigo
    elfvdm
    @0
    vg
    @1
    vy
    cv
    #
    vf
    cv
    #
    cfv
    vm
    cv
    @2
    vg
    cv
    #
    cfv
    cmul
    co
    cle
    wbr
    vy
    @3
    cdm
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
    vf
    @1
    crab
    #
    cmpt
    #
    cdm
    #
    @1
    cbigo
    @7
    vx
    vy
    vf
    vg
    vm
    df-bigo
    dmeqi
    @6
    cvv
    wcel
    #
    @8
    @1
    wceq
    vg
    @1
    vg
    @1
    @6
    cvv
    dmmptg
    @9
    @4
    @1
    wcel
    @5
    vf
    @1
    cr
    cr
    cpm
    ovex
    rabex
    a1i
    mprg
    eqtri
    syl6eleq
end
