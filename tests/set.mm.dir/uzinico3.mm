include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "uzidd.mm"
include "uzinico2.mm"
include "a1i.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "mpbird.mm"

theorem uzinico3
  let wph: wff ph
  let cM: class M
  let cZ: class Z
  assume uzinico3.1: |- ( ph -> M e. ZZ )
  assume uzinico3.2: |- Z = ( ZZ>= ` M )


  assert |- ( ph -> Z = ( Z i^i ( M [,) +oo ) ) )

  proof
    wph
    cZ
    cZ
    cM
    cpnf
    cico
    co
    #
    cin
    #
    wceq
    cM
    cuz
    cfv
    #
    @2
    @0
    cin
    #
    wceq
    wph
    cM
    cM
    wph
    cM
    uzinico3.1
    uzidd
    uzinico2
    wph
    cZ
    @2
    @1
    @3
    cZ
    @2
    wceq
    wph
    uzinico3.2
    a1i
    #
    wph
    cZ
    @2
    @0
    @4
    ineq1d
    eqeq12d
    mpbird
end
