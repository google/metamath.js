include "cv.mm"
include "cprod.mm"
include "cabs.mm"
include "cfv.mm"
include "cn.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "sselda.mm"
include "fprodzcl.mm"
include "wa.mm"
include "zcnd.mm"
include "wnel.mm"
include "wi.mm"
include "elnelne2.mm"
include "expcom.mm"
include "syl.mm"
include "imp.mm"
include "fprodn0.mm"
include "nnabscl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem absprodnn
  let wph: wff ph
  let vz: setvar z
  let cP: class P
  let cZ: class Z
  let vm: setvar m
  assume absproddvds.s: |- ( ph -> Z C_ ZZ )
  assume absproddvds.f: |- ( ph -> Z e. Fin )
  assume absproddvds.p: |- P = ( abs ` prod_ z e. Z z )
  assume absprodnn.z: |- ( ph -> 0 e/ Z )

  disjoint Z z
  disjoint ph z
  disjoint m ph
  disjoint m z
  assert |- ( ph -> P e. NN )

  proof
    wph
    cP
    cZ
    vz
    cv
    #
    vz
    cprod
    #
    cabs
    cfv
    #
    cn
    absproddvds.p
    wph
    @1
    cz
    wcel
    @1
    cc0
    wne
    @2
    cn
    wcel
    wph
    cZ
    @0
    vz
    absproddvds.f
    wph
    cZ
    cz
    @0
    absproddvds.s
    sselda
    #
    fprodzcl
    wph
    cZ
    @0
    vz
    absproddvds.f
    wph
    @0
    cZ
    wcel
    #
    wa
    @0
    @3
    zcnd
    wph
    @4
    @0
    cc0
    wne
    #
    wph
    cc0
    cZ
    wnel
    #
    @4
    @5
    wi
    absprodnn.z
    @4
    @6
    @5
    @0
    cc0
    cZ
    elnelne2
    expcom
    syl
    imp
    fprodn0
    @1
    nnabscl
    syl2anc
    syl5eqel
end
