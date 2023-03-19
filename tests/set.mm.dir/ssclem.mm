include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cdm.mm"
include "dmxpid.mm"
include "wceq.mm"
include "wfn.mm"
include "fndm.mm"
include "syl.mm"
include "adantr.mm"
include "dmexg.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "syl5eqelr.mm"
include "sqxpexg.mm"
include "fnex.mm"
include "syl2an.mm"
include "impbida.mm"

theorem ssclem
  let wph: wff ph
  let cS: class S
  let cH: class H
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cT: class T
  assume isssc.1: |- ( ph -> H Fn ( S X. S ) )


  assert |- ( ph -> ( H e. _V <-> S e. _V ) )

  proof
    wph
    cH
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    wph
    @0
    wa
    #
    cS
    cS
    cS
    cxp
    #
    cdm
    #
    cvv
    cS
    dmxpid
    @2
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @2
    cH
    cdm
    #
    @3
    cvv
    wph
    @6
    @3
    wceq
    #
    @0
    wph
    cH
    @3
    wfn
    #
    @7
    isssc.1
    @3
    cH
    fndm
    syl
    adantr
    @0
    @6
    cvv
    wcel
    wph
    cH
    cvv
    dmexg
    adantl
    eqeltrrd
    @3
    cvv
    dmexg
    syl
    syl5eqelr
    wph
    @8
    @5
    @0
    @1
    isssc.1
    cS
    cvv
    sqxpexg
    @3
    cvv
    cH
    fnex
    syl2an
    impbida
end
