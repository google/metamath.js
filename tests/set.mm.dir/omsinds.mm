include "com.mm"
include "cep.mm"
include "con0.mm"
include "wss.mm"
include "wwe.mm"
include "omsson.mm"
include "epweon.mm"
include "wess.mm"
include "mp2.mm"
include "epse.mm"
include "cv.mm"
include "wcel.mm"
include "cpred.mm"
include "wral.mm"
include "cin.mm"
include "predep.mm"
include "wceq.mm"
include "word.mm"
include "wtr.mm"
include "wi.mm"
include "ordom.mm"
include "ordtr.mm"
include "trss.mm"
include "mp2b.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqtrd.mm"
include "raleqdv.mm"
include "sylbid.mm"
include "wfis3.mm"

theorem omsinds
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume omsinds.1: |- ( x = y -> ( ph <-> ps ) )
  assume omsinds.2: |- ( x = A -> ( ph <-> ch ) )
  assume omsinds.3: |- ( x e. _om -> ( A. y e. x ps -> ph ) )

  disjoint A x
  disjoint ch x
  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( A e. _om -> ch )

  proof
    wph
    wps
    wch
    vx
    vy
    com
    cA
    cep
    com
    con0
    wss
    con0
    cep
    wwe
    com
    cep
    wwe
    omsson
    epweon
    com
    con0
    cep
    wess
    mp2
    com
    epse
    omsinds.1
    omsinds.2
    vx
    cv
    #
    com
    wcel
    #
    wps
    vy
    com
    cep
    @0
    cpred
    #
    wral
    wps
    vy
    @0
    wral
    wph
    @1
    wps
    vy
    @2
    @0
    @1
    @2
    com
    @0
    cin
    #
    @0
    com
    com
    @0
    predep
    @1
    @0
    com
    wss
    #
    @3
    @0
    wceq
    com
    word
    com
    wtr
    @1
    @4
    wi
    ordom
    com
    ordtr
    com
    @0
    trss
    mp2b
    @0
    com
    sseqin2
    sylib
    eqtrd
    raleqdv
    omsinds.3
    sylbid
    wfis3
end
