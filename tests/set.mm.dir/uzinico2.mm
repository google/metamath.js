include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "cin.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wceq.mm"
include "inass.mm"
include "a1i.mm"
include "incom.mm"
include "wss.mm"
include "uzssz.mm"
include "sseldd.mm"
include "eqid.mm"
include "uzinico.mm"
include "eqcomd.mm"
include "ineq1d.mm"
include "uzssd.mm"
include "df-ss.mm"
include "sylib.mm"
include "3eqtrd.mm"
include "mpbi.mm"
include "3eqtrrd.mm"
include "ineq1i.mm"
include "3eqtr3d.mm"

theorem uzinico2
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume uzinico2.1: |- ( ph -> N e. ( ZZ>= ` M ) )


  assert |- ( ph -> ( ZZ>= ` N ) = ( ( ZZ>= ` M ) i^i ( N [,) +oo ) ) )

  proof
    wph
    cN
    cuz
    cfv
    #
    cz
    cin
    #
    cM
    cuz
    cfv
    #
    cz
    cin
    #
    cN
    cpnf
    cico
    co
    #
    cin
    #
    @0
    @2
    @4
    cin
    #
    wph
    @5
    @2
    cz
    @4
    cin
    #
    cin
    #
    @0
    @1
    @5
    @8
    wceq
    wph
    @2
    cz
    @4
    inass
    a1i
    wph
    @8
    @7
    @2
    cin
    #
    @0
    @2
    cin
    #
    @0
    @8
    @9
    wceq
    wph
    @2
    @7
    incom
    a1i
    wph
    @7
    @0
    @2
    wph
    @0
    @7
    wph
    cN
    @0
    wph
    @2
    cz
    cN
    @2
    cz
    wss
    #
    wph
    cM
    uzssz
    #
    a1i
    uzinico2.1
    sseldd
    @0
    eqid
    uzinico
    eqcomd
    ineq1d
    wph
    @0
    @2
    wss
    @10
    @0
    wceq
    wph
    cM
    cN
    uzinico2.1
    uzssd
    @0
    @2
    df-ss
    sylib
    3eqtrd
    wph
    @1
    @0
    @1
    @0
    wceq
    #
    wph
    @0
    cz
    wss
    @13
    cN
    uzssz
    @0
    cz
    df-ss
    mpbi
    a1i
    #
    eqcomd
    3eqtrrd
    @14
    @5
    @6
    wceq
    wph
    @3
    @2
    @4
    @11
    @3
    @2
    wceq
    @12
    @2
    cz
    df-ss
    mpbi
    ineq1i
    a1i
    3eqtr3d
end
