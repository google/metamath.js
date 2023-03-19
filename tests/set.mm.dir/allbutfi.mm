include "wcel.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "ciin.mm"
include "ciun.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eliun.mm"
include "sylib.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfcxfr.mm"
include "nfel.mm"
include "wi.mm"
include "eliin.mm"
include "biimpd.mm"
include "a1d.mm"
include "reximdai.mm"
include "mpd.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "c0.mm"
include "wne.mm"
include "cz.mm"
include "eluzelz.mm"
include "uzid.mm"
include "3syl.mm"
include "ne0i.mm"
include "syl.mm"
include "eliin2.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "reximia.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "impbii.mm"

theorem allbutfi
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let cM: class M
  let cX: class X
  let cZ: class Z
  assume allbutfi.z: |- Z = ( ZZ>= ` M )
  assume allbutfi.a: |- A = U_ n e. Z |^|_ m e. ( ZZ>= ` n ) B

  disjoint X m
  disjoint X n
  disjoint m n
  assert |- ( X e. A <-> E. n e. Z A. m e. ( ZZ>= ` n ) X e. B )

  proof
    cX
    cA
    wcel
    #
    cX
    cB
    wcel
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vn
    cZ
    wrex
    #
    @0
    cX
    vm
    @2
    cB
    ciin
    #
    wcel
    #
    vn
    cZ
    wrex
    #
    @4
    @0
    cX
    vn
    cZ
    @5
    ciun
    #
    wcel
    #
    @7
    @0
    @9
    cA
    @8
    cX
    allbutfi.a
    eleq2i
    biimpi
    vn
    cX
    cZ
    @5
    eliun
    #
    sylib
    @0
    @6
    @3
    vn
    cZ
    vn
    cX
    cA
    vn
    cX
    nfcv
    vn
    cA
    @8
    allbutfi.a
    vn
    cZ
    @5
    nfiu1
    nfcxfr
    nfel
    @0
    @6
    @3
    wi
    @1
    cZ
    wcel
    #
    @0
    @6
    @3
    vm
    cX
    @2
    cB
    cA
    eliin
    biimpd
    a1d
    reximdai
    mpd
    @4
    cX
    @8
    cA
    @4
    @7
    @9
    @3
    @6
    vn
    cZ
    @11
    @3
    @6
    @11
    @3
    wa
    @6
    @3
    @11
    @3
    simpr
    @11
    @6
    @3
    wb
    #
    @3
    @11
    @2
    c0
    wne
    #
    @12
    @11
    @1
    @2
    wcel
    #
    @13
    @11
    @1
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    cz
    wcel
    @14
    @11
    @16
    cZ
    @15
    @1
    allbutfi.z
    eleq2i
    biimpi
    cM
    @1
    eluzelz
    @1
    uzid
    3syl
    @2
    @1
    ne0i
    syl
    vm
    cX
    @2
    cB
    eliin2
    syl
    adantr
    mpbird
    ex
    reximia
    @10
    sylibr
    allbutfi.a
    syl6eleqr
    impbii
end
