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
include "liminfval3.mm"

theorem liminfvaluz
  let wph: wff ph
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume liminfvaluz.k: |- F/ k ph
  assume liminfvaluz.m: |- ( ph -> M e. ZZ )
  assume liminfvaluz.z: |- Z = ( ZZ>= ` M )
  assume liminfvaluz.b: |- ( ( ph /\ k e. Z ) -> B e. RR* )

  disjoint M k
  disjoint Z k
  disjoint k x
  assert |- ( ph -> ( liminf ` ( k e. Z |-> B ) ) = -e ( limsup ` ( k e. Z |-> -e B ) ) )

  proof
    wph
    vk
    cZ
    cB
    cM
    cvv
    liminfvaluz.k
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    liminfvaluz.z
    fvexi
    a1i
    wph
    cM
    liminfvaluz.m
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
    liminfvaluz.m
    liminfvaluz.z
    uzinico3
    eqcomd
    adantr
    eleqtrd
    liminfvaluz.b
    syldan
    liminfval3
end
