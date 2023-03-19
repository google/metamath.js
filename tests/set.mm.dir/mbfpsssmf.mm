include "cmbf.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "cin.mm"
include "csmblfn.mm"
include "cfv.mm"
include "wpss.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "elinel1.mm"
include "crn.mm"
include "elinel2.mm"
include "elpmrn.mm"
include "syl.mm"
include "mbfresmf.mm"
include "ssriv.mm"
include "nsssmfmbf.mm"
include "nsstr.mm"
include "mp2an.mm"
include "pm3.2i.mm"
include "dfpss3.mm"
include "mpbir.mm"

theorem mbfpsssmf
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  assume mbfpsssmf.1: |- S = dom vol


  assert |- ( MblFn i^i ( RR ^pm RR ) ) C. ( SMblFn ` S )

  proof
    cmbf
    cr
    cr
    cpm
    co
    #
    cin
    #
    cS
    csmblfn
    cfv
    #
    wpss
    @1
    @2
    wss
    #
    @2
    @1
    wss
    wn
    #
    wa
    @3
    @4
    vf
    @1
    @2
    vf
    cv
    #
    @1
    wcel
    #
    cS
    @5
    @5
    cmbf
    @0
    elinel1
    #
    @6
    @5
    @0
    wcel
    @5
    crn
    cr
    wss
    @5
    cmbf
    @0
    elinel2
    cr
    cr
    @5
    elpmrn
    syl
    mbfpsssmf.1
    mbfresmf
    ssriv
    @2
    cmbf
    wss
    wn
    @1
    cmbf
    wss
    @4
    cS
    mbfpsssmf.1
    nsssmfmbf
    vf
    @1
    cmbf
    @7
    ssriv
    @2
    cmbf
    @1
    nsstr
    mp2an
    pm3.2i
    @1
    @2
    dfpss3
    mpbir
end
