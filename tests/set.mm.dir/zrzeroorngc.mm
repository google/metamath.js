include "czeroo.mm"
include "cfv.mm"
include "wcel.mm"
include "cinito.mm"
include "ctermo.mm"
include "zrinitorngc.mm"
include "zrtermorngc.mm"
include "cbs.mm"
include "chom.mm"
include "eqid.mm"
include "ccat.mm"
include "rngccat.mm"
include "syl.mm"
include "crng.mm"
include "cin.mm"
include "crg.mm"
include "cnzr.mm"
include "eldifad.mm"
include "ringrng.mm"
include "elind.mm"
include "rngcbas.mm"
include "eleqtrrd.mm"
include "iszeroo.mm"
include "mpbir2and.mm"

theorem zrzeroorngc
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vh: setvar h
  let vr: setvar r
  let vx: setvar x
  let vk: setvar k
  assume zrinitorngc.u: |- ( ph -> U e. V )
  assume zrinitorngc.c: |- C = ( RngCat ` U )
  assume zrinitorngc.z: |- ( ph -> Z e. ( Ring \ NzRing ) )
  assume zrinitorngc.e: |- ( ph -> Z e. U )


  assert |- ( ph -> Z e. ( ZeroO ` C ) )

  proof
    wph
    cZ
    cC
    czeroo
    cfv
    wcel
    cZ
    cC
    cinito
    cfv
    wcel
    cZ
    cC
    ctermo
    cfv
    wcel
    wph
    cC
    cU
    cV
    cZ
    zrinitorngc.u
    zrinitorngc.c
    zrinitorngc.z
    zrinitorngc.e
    zrinitorngc
    wph
    cC
    cU
    cV
    cZ
    zrinitorngc.u
    zrinitorngc.c
    zrinitorngc.z
    zrinitorngc.e
    zrtermorngc
    wph
    cC
    cbs
    cfv
    #
    cC
    cC
    chom
    cfv
    #
    cZ
    @0
    eqid
    #
    @1
    eqid
    wph
    cU
    cV
    wcel
    cC
    ccat
    wcel
    zrinitorngc.u
    cC
    cU
    cV
    zrinitorngc.c
    rngccat
    syl
    wph
    cZ
    cU
    crng
    cin
    @0
    wph
    cU
    crng
    cZ
    zrinitorngc.e
    wph
    cZ
    crg
    wcel
    cZ
    crng
    wcel
    wph
    cZ
    crg
    cnzr
    zrinitorngc.z
    eldifad
    cZ
    ringrng
    syl
    elind
    wph
    @0
    cC
    cU
    cV
    zrinitorngc.c
    @2
    zrinitorngc.u
    rngcbas
    eleqtrrd
    iszeroo
    mpbir2and
end
