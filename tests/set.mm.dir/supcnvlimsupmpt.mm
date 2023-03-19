include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cres.mm"
include "clsp.mm"
include "cli.mm"
include "wceq.mm"
include "fveq2.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "cbvmptv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "uzssd3.mm"
include "adantl.mm"
include "resmptd.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "cr.mm"
include "fmptd2f.mm"
include "supcnvlimsup.mm"
include "eqbrtrd.mm"

theorem supcnvlimsupmpt
  let wph: wff ph
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vn: setvar n
  assume supcnvlimsupmpt.j: |- F/ j ph
  assume supcnvlimsupmpt.m: |- ( ph -> M e. ZZ )
  assume supcnvlimsupmpt.z: |- Z = ( ZZ>= ` M )
  assume supcnvlimsupmpt.b: |- ( ( ph /\ j e. Z ) -> B e. RR )
  assume supcnvlimsupmpt.r: |- ( ph -> ( limsup ` ( j e. Z |-> B ) ) e. RR )

  disjoint B k
  disjoint Z j
  disjoint Z k
  disjoint j k
  disjoint B n
  disjoint k n
  disjoint Z n
  disjoint j n
  disjoint n ph
  assert |- ( ph -> ( k e. Z |-> sup ( ran ( j e. ( ZZ>= ` k ) |-> B ) , RR* , < ) ) ~~> ( limsup ` ( j e. Z |-> B ) ) )

  proof
    wph
    vk
    cZ
    vj
    vk
    cv
    #
    cuz
    cfv
    #
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
    vn
    cZ
    vj
    cZ
    cB
    cmpt
    #
    vn
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
    @6
    clsp
    cfv
    cli
    wph
    @5
    vn
    cZ
    vj
    @8
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
    @12
    vk
    vn
    cZ
    @4
    @15
    @0
    @7
    wceq
    #
    cxr
    @3
    @14
    clt
    @16
    @2
    @13
    @16
    vj
    @1
    @8
    cB
    @0
    @7
    cuz
    fveq2
    mpteq1d
    rneqd
    supeq1d
    cbvmptv
    wph
    vn
    cZ
    @15
    @11
    wph
    @7
    cZ
    wcel
    #
    wa
    #
    cxr
    @14
    @10
    clt
    @18
    @13
    @9
    @18
    @9
    @13
    @18
    vj
    cZ
    @8
    cB
    @17
    @8
    cZ
    wss
    wph
    cM
    @7
    cZ
    supcnvlimsupmpt.z
    uzssd3
    adantl
    resmptd
    eqcomd
    rneqd
    supeq1d
    mpteq2dva
    syl5eq
    wph
    vn
    @6
    cM
    cZ
    supcnvlimsupmpt.m
    supcnvlimsupmpt.z
    wph
    vj
    cZ
    cB
    cr
    supcnvlimsupmpt.j
    supcnvlimsupmpt.b
    fmptd2f
    supcnvlimsupmpt.r
    supcnvlimsup
    eqbrtrd
end
