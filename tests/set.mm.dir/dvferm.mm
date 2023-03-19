include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "cxr.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ne0i.mm"
include "ndmioo.mm"
include "necon1ai.mm"
include "3syl.mm"
include "simpld.mm"
include "clt.mm"
include "eliooord.mm"
include "syl.mm"
include "wi.mm"
include "ioossre.mm"
include "sseldi.mm"
include "rexrd.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "iooss1.mm"
include "ssralv.mm"
include "sylc.mm"
include "dvferm1.mm"
include "simprd.mm"
include "iooss2.mm"
include "dvferm2.mm"
include "wb.mm"
include "cdm.mm"
include "wf.mm"
include "dvfre.mm"
include "ffvelrnd.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem dvferm
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cX: class X
  let vz: setvar z
  let vu: setvar u
  let vx: setvar x
  let cS: class S
  let cT: class T
  assume dvferm.a: |- ( ph -> F : X --> RR )
  assume dvferm.b: |- ( ph -> X C_ RR )
  assume dvferm.u: |- ( ph -> U e. ( A (,) B ) )
  assume dvferm.s: |- ( ph -> ( A (,) B ) C_ X )
  assume dvferm.d: |- ( ph -> U e. dom ( RR _D F ) )
  assume dvferm.r: |- ( ph -> A. y e. ( A (,) B ) ( F ` y ) <_ ( F ` U ) )

  disjoint A y
  disjoint B y
  disjoint F y
  disjoint U y
  disjoint X y
  disjoint ph y
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint U u
  disjoint U x
  disjoint U z
  disjoint X u
  disjoint X x
  disjoint X z
  disjoint ph u
  disjoint S y
  disjoint S z
  disjoint T z
  assert |- ( ph -> ( ( RR _D F ) ` U ) = 0 )

  proof
    wph
    cU
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cc0
    wceq
    #
    @1
    cc0
    cle
    wbr
    #
    cc0
    @1
    cle
    wbr
    #
    wph
    vy
    cA
    cB
    cU
    cF
    cX
    dvferm.a
    dvferm.b
    dvferm.u
    dvferm.s
    dvferm.d
    wph
    cU
    cB
    cioo
    co
    #
    cA
    cB
    cioo
    co
    #
    wss
    #
    vy
    cv
    cF
    cfv
    cU
    cF
    cfv
    cle
    wbr
    #
    vy
    @6
    wral
    #
    @8
    vy
    @5
    wral
    wph
    cA
    cxr
    wcel
    #
    cA
    cU
    cle
    wbr
    #
    @7
    wph
    @10
    cB
    cxr
    wcel
    #
    wph
    cU
    @6
    wcel
    #
    @6
    c0
    wne
    @10
    @12
    wa
    #
    dvferm.u
    @6
    cU
    ne0i
    @14
    @6
    c0
    cA
    cB
    ndmioo
    necon1ai
    3syl
    #
    simpld
    #
    wph
    cA
    cU
    clt
    wbr
    #
    @11
    wph
    @17
    cU
    cB
    clt
    wbr
    #
    wph
    @13
    @17
    @18
    wa
    dvferm.u
    cU
    cA
    cB
    eliooord
    syl
    #
    simpld
    wph
    @10
    cU
    cxr
    wcel
    #
    @17
    @11
    wi
    @16
    wph
    cU
    wph
    @6
    cr
    cU
    cA
    cB
    ioossre
    dvferm.u
    sseldi
    rexrd
    #
    cA
    cU
    xrltle
    syl2anc
    mpd
    cA
    cU
    cB
    iooss1
    syl2anc
    dvferm.r
    @8
    vy
    @5
    @6
    ssralv
    sylc
    dvferm1
    wph
    vy
    cA
    cB
    cU
    cF
    cX
    dvferm.a
    dvferm.b
    dvferm.u
    dvferm.s
    dvferm.d
    wph
    cA
    cU
    cioo
    co
    #
    @6
    wss
    #
    @9
    @8
    vy
    @22
    wral
    wph
    @12
    cU
    cB
    cle
    wbr
    #
    @23
    wph
    @10
    @12
    @15
    simprd
    #
    wph
    @18
    @24
    wph
    @17
    @18
    @19
    simprd
    wph
    @20
    @12
    @18
    @24
    wi
    @21
    @25
    cU
    cB
    xrltle
    syl2anc
    mpd
    cA
    cU
    cB
    iooss2
    syl2anc
    dvferm.r
    @8
    vy
    @22
    @6
    ssralv
    sylc
    dvferm2
    wph
    @1
    cr
    wcel
    cc0
    cr
    wcel
    @2
    @3
    @4
    wa
    wb
    wph
    @0
    cdm
    #
    cr
    cU
    @0
    wph
    cX
    cr
    cF
    wf
    cX
    cr
    wss
    @26
    cr
    @0
    wf
    dvferm.a
    dvferm.b
    cX
    cF
    dvfre
    syl2anc
    dvferm.d
    ffvelrnd
    0re
    @1
    cc0
    letri3
    sylancl
    mpbir2and
end
