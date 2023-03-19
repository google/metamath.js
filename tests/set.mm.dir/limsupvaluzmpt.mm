include "cmpt.mm"
include "clsp.mm"
include "cfv.mm"
include "cv.mm"
include "cuz.mm"
include "cres.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cinf.mm"
include "fmptd2f.mm"
include "limsupvaluz.mm"
include "wceq.mm"
include "wcel.mm"
include "uzssd3.mm"
include "resmptd.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "mpteq2ia.mm"
include "a1i.mm"
include "infeq1d.mm"
include "eqtrd.mm"

theorem limsupvaluzmpt
  let wph: wff ph
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  assume limsupvaluzmpt.j: |- F/ j ph
  assume limsupvaluzmpt.m: |- ( ph -> M e. ZZ )
  assume limsupvaluzmpt.z: |- Z = ( ZZ>= ` M )
  assume limsupvaluzmpt.b: |- ( ( ph /\ j e. Z ) -> B e. RR* )

  disjoint B k
  disjoint Z j
  disjoint Z k
  disjoint j k
  assert |- ( ph -> ( limsup ` ( j e. Z |-> B ) ) = inf ( ran ( k e. Z |-> sup ( ran ( j e. ( ZZ>= ` k ) |-> B ) , RR* , < ) ) , RR* , < ) )

  proof
    wph
    vj
    cZ
    cB
    cmpt
    #
    clsp
    cfv
    vk
    cZ
    @0
    vk
    cv
    #
    cuz
    cfv
    #
    cres
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    vk
    cZ
    vj
    @2
    cB
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    wph
    vk
    @0
    cM
    cZ
    limsupvaluzmpt.m
    limsupvaluzmpt.z
    wph
    vj
    cZ
    cB
    cxr
    limsupvaluzmpt.j
    limsupvaluzmpt.b
    fmptd2f
    limsupvaluz
    wph
    cxr
    @7
    @12
    clt
    wph
    @6
    @11
    @6
    @11
    wceq
    wph
    vk
    cZ
    @5
    @10
    @1
    cZ
    wcel
    #
    cxr
    @4
    @9
    clt
    @13
    @3
    @8
    @13
    vj
    cZ
    @2
    cB
    cM
    @1
    cZ
    limsupvaluzmpt.z
    uzssd3
    resmptd
    rneqd
    supeq1d
    mpteq2ia
    a1i
    rneqd
    infeq1d
    eqtrd
end
