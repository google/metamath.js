include "cvv.mm"
include "wcel.mm"
include "cuz.mm"
include "fvexi.mm"
include "a1i.mm"
include "zred.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "cxr.mm"
include "wa.mm"
include "simpr.mm"
include "wceq.mm"
include "uzinico3.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "syldan.mm"
include "limsupval4.mm"

theorem limsupvaluz3
  let wph: wff ph
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume limsupvaluz3.k: |- F/ k ph
  assume limsupvaluz3.m: |- ( ph -> M e. ZZ )
  assume limsupvaluz3.z: |- Z = ( ZZ>= ` M )
  assume limsupvaluz3.b: |- ( ( ph /\ k e. Z ) -> B e. RR* )

  disjoint M k
  disjoint Z k
  disjoint k x
  assert |- ( ph -> ( limsup ` ( k e. Z |-> B ) ) = -e ( liminf ` ( k e. Z |-> -e B ) ) )

  proof
    wph
    vk
    cZ
    cB
    cM
    cvv
    limsupvaluz3.k
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    limsupvaluz3.z
    fvexi
    a1i
    wph
    cM
    limsupvaluz3.m
    zred
    wph
    vk
    cv
    #
    cZ
    cM
    cpnf
    cico
    co
    cin
    #
    wcel
    #
    @0
    cZ
    wcel
    cB
    cxr
    wcel
    wph
    @2
    wa
    @0
    @1
    cZ
    wph
    @2
    simpr
    wph
    @1
    cZ
    wceq
    @2
    wph
    cZ
    @1
    wph
    cM
    cZ
    limsupvaluz3.m
    limsupvaluz3.z
    uzinico3
    eqcomd
    adantr
    eleqtrd
    limsupvaluz3.b
    syldan
    limsupval4
end
