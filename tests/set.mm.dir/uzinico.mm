include "cv.mm"
include "wcel.mm"
include "cz.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wa.mm"
include "eluzelz2.mm"
include "adantl.mm"
include "cxr.mm"
include "zred.mm"
include "rexrd.mm"
include "adantr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "cr.mm"
include "zssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "sseldi.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluzle.mm"
include "syl.mm"
include "clt.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "elind.mm"
include "ex.mm"
include "elinel1.mm"
include "elinel2.mm"
include "simpr.mm"
include "icogelbd.mm"
include "syldan.mm"
include "eluzd.mm"
include "impbid.mm"
include "alrimiv.mm"
include "dfcleq.mm"
include "sylibr.mm"

theorem uzinico
  let wph: wff ph
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  assume uzinico.1: |- ( ph -> M e. ZZ )
  assume uzinico.2: |- Z = ( ZZ>= ` M )


  assert |- ( ph -> Z = ( ZZ i^i ( M [,) +oo ) ) )

  proof
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    @0
    cz
    cM
    cpnf
    cico
    co
    #
    cin
    #
    wcel
    #
    wb
    #
    vk
    wal
    cZ
    @3
    wceq
    wph
    @5
    vk
    wph
    @1
    @4
    wph
    @1
    @4
    wph
    @1
    wa
    #
    cz
    @2
    @0
    @1
    @0
    cz
    wcel
    #
    wph
    cM
    @0
    cZ
    uzinico.2
    eluzelz2
    #
    adantl
    @6
    cM
    cpnf
    @0
    wph
    cM
    cxr
    wcel
    #
    @1
    wph
    cM
    wph
    cM
    uzinico.1
    zred
    rexrd
    #
    adantr
    cpnf
    cxr
    wcel
    #
    @6
    pnfxr
    a1i
    @1
    @0
    cxr
    wcel
    wph
    @1
    cz
    cxr
    @0
    cz
    cr
    cxr
    zssre
    ressxr
    sstri
    @8
    sseldi
    adantl
    @1
    cM
    @0
    cle
    wbr
    #
    wph
    @1
    @0
    cM
    cuz
    cfv
    #
    wcel
    #
    @12
    @1
    @14
    cZ
    @13
    @0
    uzinico.2
    eleq2i
    biimpi
    cM
    @0
    eluzle
    syl
    adantl
    @1
    @0
    cpnf
    clt
    wbr
    wph
    @1
    @0
    @1
    cz
    cr
    @0
    zssre
    @8
    sseldi
    ltpnfd
    adantl
    elicod
    elind
    ex
    wph
    @4
    @1
    wph
    @4
    wa
    cM
    @0
    cZ
    uzinico.2
    wph
    cM
    cz
    wcel
    @4
    uzinico.1
    adantr
    @4
    @7
    wph
    @0
    cz
    @2
    elinel1
    adantl
    wph
    @4
    @0
    @2
    wcel
    #
    @12
    @4
    @15
    wph
    @0
    cz
    @2
    elinel2
    adantl
    wph
    @15
    wa
    #
    cM
    cpnf
    @0
    wph
    @9
    @15
    @10
    adantr
    @11
    @16
    pnfxr
    a1i
    wph
    @15
    simpr
    icogelbd
    syldan
    eluzd
    ex
    impbid
    alrimiv
    vk
    cZ
    @3
    dfcleq
    sylibr
end
