include "cmbfm.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "csiga.mm"
include "wrex.mm"
include "wfun.mm"
include "elunirnmbfm.mm"
include "biimpi.mm"
include "elmapfun.mm"
include "adantr.mm"
include "rexlimivw.mm"
include "3syl.mm"

theorem mbfmfun
  let wph: wff ph
  let cF: class F
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  assume mbfmfun.1: |- ( ph -> F e. U. ran MblFnM )


  assert |- ( ph -> Fun F )

  proof
    wph
    cF
    cmbfm
    crn
    cuni
    wcel
    #
    cF
    vt
    cv
    #
    cuni
    #
    vs
    cv
    #
    cuni
    #
    cmap
    co
    wcel
    #
    cF
    ccnv
    vx
    cv
    cima
    @3
    wcel
    vx
    @1
    wral
    #
    wa
    #
    vt
    csiga
    crn
    cuni
    #
    wrex
    #
    vs
    @8
    wrex
    #
    cF
    wfun
    #
    mbfmfun.1
    @0
    @10
    vx
    vt
    cF
    vs
    elunirnmbfm
    biimpi
    @9
    @11
    vs
    @8
    @7
    @11
    vt
    @8
    @5
    @11
    @6
    cF
    @2
    @4
    elmapfun
    adantr
    rexlimivw
    rexlimivw
    3syl
end
