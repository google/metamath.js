include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "crab.mm"
include "cfn.mm"
include "wcel.mm"
include "wceq.mm"
include "rrxbase.mm"
include "syl.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "eqsstrd.mm"
include "wral.mm"
include "wa.mm"
include "simpr.mm"
include "cvv.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "adantr.mm"
include "c0ex.mm"
include "fdmfifsupp.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "eqssd.mm"

theorem rrxbasefi
  let wph: wff ph
  let cB: class B
  let cH: class H
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  assume rrxbasefi.x: |- ( ph -> X e. Fin )
  assume rrxbasefi.h: |- H = ( RR^ ` X )
  assume rrxbasefi.b: |- B = ( Base ` H )


  assert |- ( ph -> B = ( RR ^m X ) )

  proof
    wph
    cB
    cr
    cX
    cmap
    co
    #
    wph
    cB
    vf
    cv
    #
    cc0
    cfsupp
    wbr
    #
    vf
    @0
    crab
    #
    @0
    wph
    cX
    cfn
    wcel
    #
    cB
    @3
    wceq
    rrxbasefi.x
    cB
    vf
    cH
    cX
    cfn
    rrxbasefi.h
    rrxbasefi.b
    rrxbase
    syl
    #
    @3
    @0
    wss
    wph
    @2
    vf
    @0
    ssrab2
    a1i
    eqsstrd
    wph
    @1
    cB
    wcel
    #
    vf
    @0
    wral
    @0
    cB
    wss
    wph
    @6
    vf
    @0
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @1
    @3
    cB
    @8
    @7
    @2
    wa
    @1
    @3
    wcel
    @8
    @7
    @2
    wph
    @7
    simpr
    @8
    cX
    cr
    @1
    cvv
    cc0
    @7
    cX
    cr
    @1
    wf
    wph
    @1
    cr
    cX
    elmapi
    adantl
    wph
    @4
    @7
    rrxbasefi.x
    adantr
    cc0
    cvv
    wcel
    @8
    c0ex
    a1i
    fdmfifsupp
    jca
    @2
    vf
    @0
    rabid
    sylibr
    wph
    @3
    cB
    wceq
    @7
    wph
    cB
    @3
    @5
    eqcomd
    adantr
    eleqtrd
    ralrimiva
    vf
    @0
    cB
    dfss3
    sylibr
    eqssd
end
