include "cmnf.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "cin.mm"
include "cioo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "adantr.mm"
include "elinel2.mm"
include "adantl.mm"
include "mnfltd.mm"
include "elinel1.mm"
include "icoltubd.mm"
include "eliood.mm"
include "ssd.mm"
include "wss.mm"
include "ioossico.mm"
include "ioossre.mm"
include "ssini.mm"
include "eqssd.mm"

theorem icomnfinre
  let wph: wff ph
  let cA: class A
  let vx: setvar x
  assume icomnfinre.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> ( ( -oo [,) A ) i^i RR ) = ( -oo (,) A ) )

  proof
    wph
    cmnf
    cA
    cico
    co
    #
    cr
    cin
    #
    cmnf
    cA
    cioo
    co
    #
    wph
    vx
    @1
    @2
    wph
    vx
    cv
    #
    @1
    wcel
    #
    wa
    #
    cmnf
    cA
    @3
    cmnf
    cxr
    wcel
    @5
    mnfxr
    a1i
    #
    wph
    cA
    cxr
    wcel
    @4
    icomnfinre.1
    adantr
    #
    @4
    @3
    cr
    wcel
    wph
    @3
    @0
    cr
    elinel2
    adantl
    #
    @5
    @3
    @8
    mnfltd
    @5
    cmnf
    cA
    @3
    @6
    @7
    @4
    @3
    @0
    wcel
    wph
    @3
    @0
    cr
    elinel1
    adantl
    icoltubd
    eliood
    ssd
    @2
    @1
    wss
    wph
    @2
    @0
    cr
    cmnf
    cA
    ioossico
    cmnf
    cA
    ioossre
    ssini
    a1i
    eqssd
end
