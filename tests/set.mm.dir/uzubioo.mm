include "cceil.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cpnf.mm"
include "cioo.mm"
include "wcel.mm"
include "cv.mm"
include "wrex.mm"
include "rexrd.mm"
include "cxr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "cr.mm"
include "ceilcld.mm"
include "1zzd.mm"
include "zaddcld.mm"
include "zred.mm"
include "ifcld.mm"
include "ceilged.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "max2d.mm"
include "ltletrd.mm"
include "ltpnfd.mm"
include "eliood.mm"
include "cz.mm"
include "max1.mm"
include "syl2anc.mm"
include "eluzd.mm"
include "eleq1.mm"
include "rspcev.mm"

theorem uzubioo
  let wph: wff ph
  let vk: setvar k
  let cM: class M
  let cX: class X
  let cZ: class Z
  assume uzubioo.1: |- ( ph -> M e. ZZ )
  assume uzubioo.2: |- Z = ( ZZ>= ` M )
  assume uzubioo.3: |- ( ph -> X e. RR )

  disjoint M k
  disjoint X k
  disjoint Z k
  assert |- ( ph -> E. k e. ( X (,) +oo ) k e. Z )

  proof
    wph
    cM
    cX
    cceil
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @1
    cM
    cif
    #
    cX
    cpnf
    cioo
    co
    #
    wcel
    @3
    cZ
    wcel
    #
    vk
    cv
    #
    cZ
    wcel
    #
    vk
    @4
    wrex
    wph
    cX
    cpnf
    @3
    wph
    cX
    uzubioo.3
    rexrd
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    @2
    @1
    cM
    cr
    wph
    @1
    wph
    @0
    c1
    wph
    cX
    uzubioo.3
    ceilcld
    #
    wph
    1zzd
    zaddcld
    #
    zred
    #
    wph
    cM
    uzubioo.1
    zred
    #
    ifcld
    #
    wph
    cX
    @1
    @3
    uzubioo.3
    @10
    @12
    wph
    cX
    @0
    @1
    uzubioo.3
    wph
    @0
    @8
    zred
    #
    @10
    wph
    cX
    uzubioo.3
    ceilged
    wph
    @0
    @13
    ltp1d
    lelttrd
    wph
    cM
    @1
    @11
    @10
    max2d
    ltletrd
    wph
    @3
    @12
    ltpnfd
    eliood
    wph
    cM
    @3
    cZ
    uzubioo.2
    uzubioo.1
    wph
    @2
    @1
    cM
    cz
    @9
    uzubioo.1
    ifcld
    wph
    cM
    cr
    wcel
    @1
    cr
    wcel
    cM
    @3
    cle
    wbr
    @11
    @10
    cM
    @1
    max1
    syl2anc
    eluzd
    @7
    @5
    vk
    @3
    @4
    @6
    @3
    cZ
    eleq1
    rspcev
    syl2anc
end
