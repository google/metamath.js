include "cpnf.mm"
include "wcel.mm"
include "cmnf.mm"
include "wo.mm"
include "cr.mm"
include "wss.mm"
include "wn.mm"
include "w3o.mm"
include "cxr.mm"
include "ssxr.mm"
include "syl.mm"
include "3orass.mm"
include "sylib.mm"
include "orcomd.mm"
include "wa.mm"
include "jca.mm"
include "ioran.mm"
include "sylibr.mm"
include "wi.mm"
include "df-or.mm"
include "biimpi.mm"
include "sylc.mm"

theorem xrssre
  let wph: wff ph
  let cA: class A
  assume xrssre.1: |- ( ph -> A C_ RR* )
  assume xrssre.2: |- ( ph -> -. +oo e. A )
  assume xrssre.3: |- ( ph -> -. -oo e. A )


  assert |- ( ph -> A C_ RR )

  proof
    wph
    cpnf
    cA
    wcel
    #
    cmnf
    cA
    wcel
    #
    wo
    #
    cA
    cr
    wss
    #
    wo
    #
    @2
    wn
    #
    @3
    wph
    @3
    @2
    wph
    @3
    @0
    @1
    w3o
    #
    @3
    @2
    wo
    wph
    cA
    cxr
    wss
    @6
    xrssre.1
    cA
    ssxr
    syl
    @3
    @0
    @1
    3orass
    sylib
    orcomd
    wph
    @0
    wn
    #
    @1
    wn
    #
    wa
    @5
    wph
    @7
    @8
    xrssre.2
    xrssre.3
    jca
    @0
    @1
    ioran
    sylibr
    @4
    @5
    @3
    wi
    @2
    @3
    df-or
    biimpi
    sylc
end
